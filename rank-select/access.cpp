#include <iostream>
#include <fstream>
#include <vector>
#include <algorithm>
#include <cassert>
#include <cmath>
#include <random>
#include <chrono>
#include "posix_file.cpp"

using namespace std;
using namespace std::chrono;

template <class T>
static void debug(T x) {
  bool seen = false;
  for (uint64_t index = sizeof(T) * 8; index; --index) {
#if 0
    seen |= ((x >> (index - 1)) & 1);
    if (seen) {
      std::cerr << ((x >> (index - 1)) & 1);
    }
#else
      std::cerr << ((x >> (index - 1)) & 1);
#endif
  }
  std::cerr << std::endl;
}

uint64_t smallestPowerOfTwoGt(uint64_t x) {
  return (1 << ((x & (x - 1)) != 0)) * static_cast<uint64_t>(std::log2(x));
}

template <class T>
auto randomNumberBetween = [](T low, T high) {
  auto randomFunc = [distribution_ = std::uniform_int_distribution<T>(low, high), random_engine_ = std::mt19937{std::random_device{}()}]() mutable {
    return distribution_(random_engine_);
  };
  return randomFunc;
};

template <class T>
static std::vector<T> generator(uint64_t size, T maxValue) {
  vector<T> numbers;
  std::generate_n(std::back_inserter(numbers), size, randomNumberBetween<T>(0, maxValue));
  return numbers;
}

std::string getDataFilename(std::string directory) {
  return directory + "/data.bin";
}

template <class T>
void createData(std::string directory = ".", uint64_t memsize = (1u << 20) * 512) {
  uint64_t size = static_cast<uint64_t>(memsize / sizeof(T));
  if (!size)
    size = 1;
  std::cerr << "Creating data.." << std::endl;
  std::vector<T> keys = generator<T>(size, std::numeric_limits<T>::max());
  std::ofstream outputKeys(directory + "/data.bin");
  outputKeys.write(reinterpret_cast<char*>(keys.data()), keys.size() * sizeof(T));
  outputKeys.close();
  
#if 0
  for (auto key : keys)
    debug(key);
#endif
  
#if 1
  std::cerr << "Generated " << size << " keys of " << sizeof(T) << " bytes each!" << std::endl;
#endif
  
  vector<uint64_t> queries = generator<uint64_t>(1e6, size - 1);
  std::ofstream outputQueries(directory + "/queries.bin");
  outputQueries.write(reinterpret_cast<char*>(queries.data()), queries.size() * sizeof(uint64_t));
  outputQueries.close();
  
  auto offline = [&](std::vector<uint64_t>& answers) -> void {
    auto getBit = [&](uint64_t index) {
      uint64_t bucketIndex = index / (sizeof(T) * 8);
      index -= bucketIndex * sizeof(T) * 8;
      return (keys[bucketIndex] >> (sizeof(T) * 8 - index - 1)) & 1;
    };
    auto currSize = queries.size();
    answers.resize(currSize);
    std::vector<std::pair<uint64_t, uint64_t>> tmp(currSize);
    for (unsigned index = 0, limit = currSize; index != limit; ++index)
      tmp[index] = std::make_pair(queries[index], index);
    std::sort(tmp.begin(), tmp.end());
    std::optional<uint64_t> lastQuery;
    uint64_t answer = 0;
    auto count = 0;
    for (auto elem : tmp) {
      auto query = elem.first;
      if (lastQuery.has_value() && lastQuery.value() == query) {
        answers[elem.second] = answer;
        continue;
      }
      for (uint64_t index = lastQuery.has_value() ? (lastQuery.value() + 1) : 0; index <= query; ++index)
        answer += getBit(index);
      answers[elem.second] = answer;
      lastQuery = query;
    }
  };
  
  vector<uint64_t> answers; offline(answers);
  std::ofstream outputAnswers(directory + "/answers.bin");
  outputAnswers.write(reinterpret_cast<char*>(answers.data()), answers.size() * sizeof(uint64_t));
  outputAnswers.close();
  std::cerr << "Finished creating data!" << std::endl;
}

template <class T>
void loadVector(std::vector<T>& v, std::string filename) {
  ifstream in(filename);
  auto pos = in.tellg();
  in.seekg(0, ios::end);  
  auto size = in.tellg() - pos;
  in.seekg(0, ios::beg);
  uint64_t elements = size / sizeof(T);
  v.resize(elements);
  in.read(reinterpret_cast<char*>(v.data()), elements * sizeof(T));
}

template <class T>
void loadData(std::string directory, std::vector<uint64_t>& qs, std::vector<uint64_t>& as) {
  std::cerr << "Loading data.." << std::endl;
  loadVector(qs, directory + "/queries.bin");
  loadVector(as, directory + "/answers.bin");
  std::cerr << "Finished loading data!" << std::endl;
}

namespace succint {

template <class T>
class RankSelect {
public:
  class RankLookupTable {
    friend class RankSelect<T>;
    size_t x;
    // TODO: pack the bits for the same bit configuration
    vector<vector<unsigned>> table;
    RankLookupTable(size_t x) : x(x) {
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

  class RankReducer {
    friend class RankSelect<T>;
    RankSelect<T>* master;
    uint64_t startIndex, stopIndex, reductionSize;
    std::vector<pair<unsigned, uint64_t>> reduction;
    RankReducer(RankSelect* master, uint64_t startIndex) : master(master), startIndex(startIndex) {
      stopIndex = (master->rankIndirectionSize > master->size - startIndex) ? master->size : (startIndex + master->rankIndirectionSize);
      reductionSize = this->master->rankTable->x;
      processReduction();
    }
    
    void processReduction() {
      uint64_t curr = 0, prev = 0;
      unsigned builder = 0;
      //std::cerr << "PROCESS: " << startIndex << " -> " << stopIndex << std::endl;
      for (uint64_t index = startIndex; index != stopIndex; ++index) {
        if ((index != startIndex) && ((index - startIndex) % reductionSize == 0)) {
          reduction.push_back(make_pair(builder, prev));
          prev = curr;
          builder = 0;
        }
        //std::cerr << "index=" << index << " -> " << master->access(index) << std::endl;
        builder = (builder << 1) + master->access(index);
        curr += master->access(index);
      }
      uint64_t mod = (stopIndex - startIndex) % reductionSize;
      if (mod)
        builder <<= (reductionSize - mod);
      reduction.push_back(make_pair(builder, prev));
    }
    
    uint64_t query(uint64_t pos) {
      assert(startIndex <= pos && pos < stopIndex);
      uint64_t reductionBlock = (pos - startIndex) / reductionSize;
      uint64_t partial = reduction[reductionBlock].second;
#if 0
      std::cerr << "reductionSize=" << reductionSize << " total=" << (stopIndex - startIndex) << std::endl;
      std::cerr << "partial=" << partial << std::endl;
      std::cerr << "slot=" << reduction[reductionBlock].first << std::endl;
      std::cerr << "position=" << (pos - startIndex) % reductionSize << std::endl;
#endif
      uint64_t lookup = this->master->rankTable->access(reduction[reductionBlock].first, (pos - startIndex) % reductionSize);
      return partial + lookup;
    }
  };
  
  uint64_t lg, lglg, size, total, rankIndirectionSize, currentBucketIndex;
  RankLookupTable* rankTable;
  std::vector<T> chunk;
  std::vector<pair<RankReducer*, uint64_t>> rankIndirection;
  
  RankSelect(std::string& directory) {
    std::string filename = getDataFilename(directory);
    PosixFile file(filename.data(), File::READ);
    
    std::cerr << "Building the succint structure.." << std::endl;
    size = file.size() * 8;

    // Create the tables
    lg = static_cast<uint64_t>(std::log2(size));
    std::cerr << "lg=" << lg << std::endl;
    rankTable = new RankLookupTable((2 + lg) >> 1);
    
    std::cerr << "Size of table=" << rankTable->x << std::endl;
    
    // Build the indirections
    processRankIndirection(file);
    std::cerr << "Finished!" << std::endl;
  }
  
  uint64_t access(uint64_t index) {
    uint64_t bucketIndex = index / (sizeof(T) * 8);
    index -= bucketIndex * sizeof(T) * 8;
    return (chunk[bucketIndex - currentBucketIndex] >> (sizeof(T) * 8 - index - 1)) & 1;
  }
  
  void processRankIndirection(File& file) {
    rankIndirectionSize = lg * lg;
    currentBucketIndex = 0;
    chunk.resize(2 + ((rankIndirectionSize) / 8) / sizeof(T));
    
    auto require = [&](uint64_t a, uint64_t b) -> uint64_t {
      // Require the memory
      currentBucketIndex = a / (sizeof(T) * 8);
      uint64_t ap = currentBucketIndex, bp = b / (sizeof(T) * 8);
      if ((bp - ap + 1) > chunk.size()) {
        std::cerr << "a=" << a << " b=" << b << " chunk=" << chunk.size() << std::endl;
      }
      file.read_block(ap * sizeof(T), (bp - ap + 1) * sizeof(T), reinterpret_cast<char*>(chunk.data()));
      
      // Sum up the values in [a, b[
      uint64_t sum = 0;
      for (uint64_t index = a; index != b; ++index) {
        //std::cerr << index << " -> " << access(index) << std::endl;
        sum += access(index);
      }
      //std::cerr << "a=" << a << " b=" << b << " sum=" << sum << std::endl;
      return sum;
    };
    
    // And compute
    uint64_t curr = 0;
    for (uint64_t index = rankIndirectionSize; index != size; index += ((rankIndirectionSize >= (size - index)) ? (size - index) : rankIndirectionSize)) {
      // Compute the sum between the two indices
      uint64_t tmp = require(index - rankIndirectionSize, index);
      auto reducer = new RankReducer(this, index - rankIndirectionSize);
      rankIndirection.push_back(make_pair(reducer, curr));
      curr += tmp;
    }
    uint64_t last = (size % rankIndirectionSize == 0) ? rankIndirectionSize : (size % rankIndirectionSize);
    require(size - last, size);
    auto reducer = new RankReducer(this, size - last);
    rankIndirection.push_back(make_pair(reducer, curr));
  }

  uint64_t succintRank(uint64_t pos) {
    // #1's at or before 'pos'
    assert((0 <= pos) && (pos < size));
    uint64_t indirectionBlock = pos / rankIndirectionSize;
    uint64_t partial = rankIndirection[indirectionBlock].second;
    //std::cerr << "partial global=" << partial << std::endl;
    auto reducer = rankIndirection[indirectionBlock].first;
    return partial + reducer->query(pos);
  }
  
  uint64_t succintSelect(uint64_t x) {
#if 0
    assert((1 <= x) && (x <= total));
    return x;
#else
    assert(0);
#endif
  }

#if 0 
  uint64_t naiveRank(uint64_t pos) {
    // #1's at or before 'pos'
    assert((0 <= pos) && (pos < size));
    auto ret = 0;
    for (uint64_t index = 0; index <= pos; ++index)
      ret += access(index);
    return ret;
  }

  uint64_t naiveSelect(uint64_t x) {
    // Position of xth bit
    assert((1 <= x) && (x <= total));
    auto count_ = 0;
    for (uint64_t index = 0; index != size; ++index) {
      count_ += access(index);
      if (count_ == x)
        return index;
    }
    return size;
  }
#endif
};

}

template <class T>
void benchmark(std::string directory = ".") {
  std::vector<uint64_t> queries, answers;
  loadData<T>(directory, queries, answers);
  
  typedef std::ratio<1l, 1000000000000l> pico;
  typedef duration<long long, pico> picoseconds;
  
  succint::RankSelect<T> rs(directory);
  auto start = high_resolution_clock::now();
  for (uint64_t index = 0, limit = queries.size(); index != limit; ++index) {
    uint64_t a = answers[index], ret = rs.succintRank(queries[index]);
    if (a != ret)
      std::cerr << "q=" << queries[index] << " out=" << ret << " vs ok=" << a << std::endl;
    assert(a == ret);
  }
  auto stop = high_resolution_clock::now();
  auto answer = duration_cast<picoseconds>(stop - start).count() / queries.size();
  auto len = std::to_string(answer % 1000).size();
  auto ret = std::to_string(answer / 1000) + "." + (len == 1 ? "00" : (len == 2 ? "0" : "")) + to_string(answer % 1000) + " ps";
  std::cerr << "Query: " << ret << std::endl;
}

int main(int argc, char** argv) {
  if (argc != 2) {
    std::cerr << "Usage: " << argv[0] << " [0|1|filename] (createFile | benchmark | custom data)" << std::endl;
    exit(-1);
  } else if (argc == 2) {
    auto op = atoi(argv[1]);
    if (!op) {
#if 0
      std::cerr << "Are you sure you want to create new data? (y | n)" << std::endl;
      std::string str;
      std::cin >> str;
      assert(str.length() == 1);
      if (str[0] == 'n')
        exit(0);
#endif
      createData<uint64_t>();
    } else
      benchmark<uint64_t>();
  }
  return 0;
}
