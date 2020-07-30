#include <iostream>
#include <fstream>
#include <vector>
#include <cassert>
#include <cmath>

using namespace std;

class LookupTable {
  friend class RankSelect;
  size_t x;
  // TODO: pack the bits for the same bit configuration
  vector<vector<unsigned>> table;
  LookupTable(unsigned x) : x(x) {
    assert(x <= 30);
    process();
  }
  
  void process() {
    table.resize(1u << x);
    // For each possible bit configuration of length x
    for (unsigned index = 0; index != (1u << x); ++index) {
      // Precompute the results
      table[index].resize(x);
      for (unsigned curr = 0, ptr = 0; ptr != x; ++ptr) {
        curr += ((index >> (x - ptr - 1)) & 1);
        table[index][ptr] = curr;
      }
    }
  }
  
  unsigned access(unsigned slot, unsigned pos) {
    return table[slot][pos];
  }
};

class RankSelect {
public:
  class Reducer {
    friend class RankSelect;
    RankSelect* master;
    unsigned startIndex, stopIndex, reductionSize;
    std::vector<pair<unsigned, unsigned>> reduction;
    Reducer(RankSelect* master, unsigned startIndex) {
      this->master = master;
      stopIndex = std::min(startIndex + master->indirectionSize, master->size);
      reductionSize = (1 + this->master->lg) / 2;
      processReduction();
    }
    
    void processReduction() {
      auto curr = 0, builder = 0;
      for (unsigned index = startIndex; index != stopIndex; ++index) {
        if ((index != startIndex) && ((index - startIndex) % reductionSize == 0)) {
          reduction.push_back(make_pair(builder, curr));
          curr = 0;
        }
        builder = (builder << 1) + master->bitvector[index];
        curr += master->bitvector[index];
      }
      auto mod = (stopIndex - startIndex) % reductionSize;
      if (!mod) {
        reduction.push_back(make_pair(builder, curr));
      } else {
        builder <<= (reductionSize - mod);
        reduction.push_back(make_pair(builder, curr));
      }
    }
    
    unsigned query(unsigned pos) {
      assert((startIndex <= pos) && (pos < stopIndex));
      auto reductionBlock = (pos - startIndex) / reductionSize;
      auto partial = reduction[reductionBlock].second;
      auto lookup = this->master->table->access(reduction[reductionBlock].first, (pos - startIndex) % reductionSize);
      return partial + lookup;
    }
  };

  size_t lg, size, total, indirectionSize;
  LookupTable* table;
  std::vector<unsigned> bitvector;
  std::vector<pair<Reducer*, unsigned>> indirection;
  RankSelect(std::vector<unsigned> bitvector) : bitvector(bitvector), size(bitvector.size()) {
    total = 0;
    for (auto bit : bitvector)
      total += bit;
    lg = static_cast<unsigned>(std::log2(size));
    std::cerr << "before init" << std::endl;
    std::cerr << "lg=" << lg << endl;
    table = new LookupTable((1 + lg) >> 1);
    std::cerr << "after init" << std::endl;
    indirectionSize = lg * lg;
    processIndirection();
  }
  
  void processIndirection() {
    auto curr = 0;
    for (unsigned index = 0; index != size; ++index) {
      if ((index) && (index % indirectionSize == 0)) {
        auto reducer = new Reducer(this, index - indirectionSize);
        indirection.push_back(make_pair(reducer, curr));
        curr = 0;
      }
      curr += bitvector[index];
    }
    auto last = (size % indirectionSize == 0) ? (size - indirectionSize) : ((size / indirectionSize) * indirectionSize);
    auto reducer = new Reducer(this, last);
    indirection.push_back(make_pair(reducer, curr));
  }

  unsigned succintRank(unsigned pos) {
    // #1's ar or before 'pos'
    assert((0 <= pos) && (pos < size));
    auto indirectionBlock = pos / indirectionSize;
    auto partial = indirection[indirectionBlock].second;
    auto reducer = indirection[indirectionBlock].first;
    return partial + reducer->query(pos);
  }
  
  unsigned succintSelect(unsigned x) {
    assert((1 <= x) && (x <= total));
    return x;
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
      if (bitvector[index])
        count_++;
      if (count_ == x)
        return index;
    }
    return size;
  }
};

int main(void) {
  ifstream input("1.in");
  string str;
  cin >> str;
  vector<unsigned> bitvector(str.size());
  for (unsigned index = 0; index != str.size(); ++index)
    bitvector[index] = str[index] - '0';
  RankSelect rs(bitvector);
  unsigned m;
  cin >> m;
  while (m--) {
    char type; unsigned x;
    cin >> type >> x;
    if (type == 'r') {
      cout << rs.succintRank(x) << endl;
    } else {
      cout << rs.succintSelect(x) << endl;
    }
  }
  return 0;
}
