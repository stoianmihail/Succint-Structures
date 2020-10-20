#include <iostream>
#include <fstream>
#include <vector>
#include <cassert>
#include <cmath>

using namespace std;

static void debug(unsigned x) {
  bool seen = false;
  for (unsigned index = 32; index; --index) {
    seen |= ((x >> (index - 1)) & 1);
    if (seen) {
      std::cerr << ((x >> (index - 1)) & 1);
    }
  }
  std::cerr << std::endl;
}

class RankLookupTable {
  size_t x;
  // TODO: pack the bits for the same bit configuration
  vector<vector<unsigned>> table;
  RankLookupTable(unsigned x) : x(x) {
    assert(x <= 30);
    process();
  }
  
  void process() {
    table.resize(1u << x);
    // For each possible bit string of length x
    for (unsigned index = 0; index != (1u << x); ++index) {
      // Precompute the results on the inverted bit string
      table[index].resize(x);
      for (unsigned curr = 0, ptr = 0; ptr != x; ++ptr) {
        curr += ((index >> (x - ptr - 1)) & 1);
        table[index][ptr] = curr;
      }
    }
  }
  
  unsigned access(unsigned slot, unsigned pos) {
    assert((slot < (1u << x)) && (pos < x));
    return table[slot][pos];
  }
};

class SelectLookupTable {
  friend class RankSelect;
  
  size_t x;
  vector<vector<unsigned>> table;
  SelectLookupTable(unsigned x) : x(x) {
    assert(x <= 30);
    process();
  }
  
  void process() {
    table.resize(1u << x);
    for (unsigned index = 0; index != (1u << x); ++index) {
      auto count = __builtin_popcount(index);
      table[index].resize(count);
      for (unsigned ptr = 0, curr = 0; ptr != x; ++ptr)
        ((index >> (x - ptr - 1)) & 1) && (table[index][curr++] = ptr);
    }
  }
  
  unsigned access(unsigned slot, unsigned index) {
    assert((slot < (1u << x)) && (index < table[slot].size()));
    return table[slot][index];
  }
};

class RankSelect {
public:
  class RankReducer {
    RankSelect* master;
    unsigned startIndex, stopIndex, reductionSize;
    std::vector<pair<unsigned, unsigned>> reduction;
    RankReducer(RankSelect* master, unsigned startIndex) : master(master), startIndex(startIndex) {
      stopIndex = std::min(startIndex + master->rankIndirectionSize, master->size);
      reductionSize = this->master->rankTable->x;
      processReduction();
    }
    
    void processReduction() {
      auto curr = 0, prev = 0, builder = 0;
      for (unsigned index = startIndex; index != stopIndex; ++index) {
        if ((index != startIndex) && ((index - startIndex) % reductionSize == 0)) {
          reduction.push_back(make_pair(builder, prev));
          prev = curr;
          builder = 0;
        }
        builder = (builder << 1) + master->bitvector[index];
        curr += master->bitvector[index];
      }
      auto mod = (stopIndex - startIndex) % reductionSize;
      if (!mod)
        builder <<= (reductionSize - mod);
      reduction.push_back(make_pair(builder, curr));
    }
    
    unsigned query(unsigned pos) {
      assert((startIndex <= pos) && (pos < stopIndex));
      auto reductionBlock = (pos - startIndex) / reductionSize;
      auto partial = reduction[reductionBlock].second;
      auto lookup = this->master->rankTable->access(reduction[reductionBlock].first, (pos - startIndex) % reductionSize);
      return partial + lookup;
    }
  };
  
  class SelectReducer {
    class DeepReducer {
      SelectReducer* master;
      bool isSparse = false;
      size_t startIndex, stopIndex, localSize, lookupIndex;
      std::vector<unsigned> indices;
      DeepReducer(SelectReducer* master, unsigned startIndex, unsigned stopIndex) : master(master), startIndex(startIndex), stopIndex(stopIndex) {
        localSize = stopIndex - startIndex;
        processReduction();
      }
      
      void processReduction() {
        // Is sparse?
        if ((stopIndex - startIndex) > master->localIndirectionSize * master->localIndirectionSize) {
          isSparse = true;
          indices.reserve(master->localIndirectionSize);
          for (unsigned ptr = 0, curr = 0; ptr != localSize; ++ptr)
            if (master->master->bitvector[ptr + startIndex])
              indices.push_back(ptr + startIndex);
        } else {
          // It's dense (r <= (lglgn)^4) -> use the 'SelectLookupTable'
          lookupIndex = 0;
          for (unsigned ptr = 0, curr = 0; ptr != localSize; ++ptr)
            lookupIndex = (lookupIndex << 1) + master->master->bitvector[ptr + startIndex];
        }
      }
      
      unsigned query(unsigned index) {
        if (isSparse) {
          assert(index < indices.size());
          return indices[index];
        } else {
          return master->master->selectTable->access(lookupIndex, index);
        }
      }
    };

    RankSelect* master;
    bool isSparse = false;
    size_t startIndex, stopIndex, localSize, localIndirectionSize;
    std::vector<unsigned> indices;
    std::vector<DeepReducer*> further;
    SelectReducer(RankSelect* master, unsigned startIndex, unsigned stopIndex) : master(master), startIndex(startIndex), stopIndex(stopIndex) {
      localSize = stopIndex - startIndex;
      processReduction();
    }
    
    void processReduction() {
      // Is sparse?
      if ((stopIndex - startIndex) > master->selectIndirectionSize * master->selectIndirectionSize) {
        isSparse = true;
        // There could be the case that we receive exactly the last group, where the number of 1's might be lower
        indices.reserve(master->selectIndirectionSize);
        for (unsigned ptr = 0, curr = 0; ptr != localSize; ++ptr)
          if (master->bitvector[ptr + startIndex])
            indices.push_back(ptr + startIndex);
      } else {
        // This is a group of at most (lgn lglgn)^2 bits, so repeat the same indirection as in 'master'
        // Store the realtive index of every (lglgn)^2
        auto count = 0;
        localIndirectionSize = master->lglg * master->lglg;
        for (unsigned ptr = 0; ptr != localSize; ++ptr) {
          count += master->bitvector[ptr + startIndex];
          if ((count + 1) % localIndirectionSize)
            indices.push_back(ptr);
        }
        if ((indices.empty()) || (indices.back() != localSize - 1))
          indices.push_back(localSize - 1);
        for (unsigned index = 0, last = 0, limit = indices.size(); index != limit; ++index) {
          DeepReducer* curr = DeepReducer(this, last, indices[index]);
          further.push_back(curr);
          last = indices[index] + 1;
        }
        indices.clear();
      }
    }
    
    unsigned query(unsigned index) {
      if (isSparse) {
        assert(index < indices.size());
        return indices[index];
      } else {
        auto oneBlockIndex = index / localIndirectionSize;
        return further[oneBlockIndex]->query(index % localIndirectionSize);
      }
    }
  };

  size_t lg, lglg, size, total, rankIndirectionSize, selectIndirectionSize;
  RankLookupTable* rankTable;
  SelectLookupTable* selectTable;
  std::vector<unsigned> bitvector;
  std::vector<pair<RankReducer*, unsigned>> rankIndirection;
  std::vector<SelectReducer*> selectIndirection;
  
  friend class RankReducer;
  friend class SelectReducer;
  
  RankSelect(std::vector<unsigned> bitvector) : bitvector(bitvector), size(bitvector.size()) {
    total = 0;
    for (auto bit : bitvector)
      total += bit;
    
    // Create the tables
    lg = static_cast<unsigned>(std::log2(size));
    rankTable = new RankLookupTable((2 + lg) >> 1);
    selectTable = new SelectLookupTable((2 + lg) >> 1);
    
    // Build the indirections
    processRankIndirection();
    processSelectIndirection();
  }
  
  void processRankIndirection() {
    rankIndirectionSize = lg * lg;
    auto curr = 0, prev = 0;
    for (unsigned index = 0; index != size; ++index) {
      if ((index) && (index % rankIndirectionSize == 0)) {
        auto reducer = new RankReducer(this, index - rankIndirectionSize);
        rankIndirection.push_back(make_pair(reducer, prev));
        prev = curr;
      }
      curr += bitvector[index];
    }
    auto last = (size % rankIndirectionSize == 0) ? rankIndirectionSize : (size % rankIndirectionSize);
    auto reducer = new RankReducer(this, last);
    rankIndirection.push_back(make_pair(reducer, curr));
  }

  void processSelectIndirection() {
    lglg = static_cast<unsigned>(std::log2(size));
    if (!lglg)
      lglg = 1;
    selectIndirectionSize = lg * lglg;
    auto count = 0;
    std::vector<unsigned> indices;
    for (unsigned index = 0; index != size; ++index) {
      count += bitvector[index];
      if ((count + 1) % selectIndirectionSize == 0)
        indices.push_back(index);
    }
    if ((indices.empty()) || (indices.back() != size - 1))
      indices.push_back(size - 1);
    for (unsigned index = 0, last = 0, limit = indices.size(); index != limit; ++index) {
      auto reducer = new SelectReducer(this, last, indices[index]);
      selectIndirection.push_back(reducer);
      last = indices[index] + 1;
    }
    indices.clear();
  }
  
  unsigned succintRank(unsigned pos) {
    // #1's ar or before 'pos'
    assert((0 <= pos) && (pos < size));
    auto indirectionBlock = pos / rankIndirectionSize;
    auto partial = rankIndirection[indirectionBlock].second;
    auto reducer = rankIndirection[indirectionBlock].first;
    std::cerr << "partial=" << partial << std::endl;
    return partial + reducer->query(pos % rankIndirectionSize);
  }
  
  unsigned succintSelect(unsigned x) {
    assert((1 <= x) && (x <= total));
    auto oneBlockIndex = (x - 1) / selectIndirectionSize;
    return selectIndirection[oneBlockIndex]->query((x - 1) % selectIndirectionSize);
  }
  
  unsigned naiveRank(unsigned pos) {
    // #1's ar or before 'pos'
    assert((0 <= pos) && (pos < size));
    auto ret = 0;
    for (unsigned index = 0; index <= pos; ++index)
      ret += bitvector[index];
    return ret;
  }

  unsigned naiveSelect(unsigned x) {
    // Position of xth bit
    assert((1 <= x) && (x <= total));
    auto count_ = 0;
    for (unsigned index = 0; index != size; ++index) {
      count_ += bitvector[index];
      if (count_ == x)
        return index;
    }
    return size;
  }
};

int main(void) {
  ifstream inputFile("1.in");
  ifstream answerFile("1.ok");
  string str;
  inputFile >> str;
  vector<unsigned> bitvector(str.size());
  for (unsigned index = 0; index != str.size(); ++index)
    bitvector[index] = str[index] - '0';
  RankSelect rs(bitvector);
  unsigned m;
  inputFile >> m;
  while (m--) {
    unsigned ans;
    answerFile >> ans;
    char type; unsigned x;
    inputFile >> type >> x;
    if (type == 'r') {
      auto ret = rs.succintRank(x);
      assert(ret == rs.naiveRank(x));
      assert(ret == ans);
    } else {
      auto ret = rs.succintSelect(x);
      assert(ret == rs.naiveSelect(x));
      assert(ret == ans);
    }
  }
  return 0;
}
