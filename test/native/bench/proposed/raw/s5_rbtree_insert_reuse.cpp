#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <map>
#include <vector>

int main(int argc, char **argv) {
  int n = argc > 1 ? std::atoi(argv[1]) : 12000;
  std::map<int, int> m;
  struct Range { int lo; int hi; };
  std::vector<Range> stack;
  stack.push_back({1, n});
  while (!stack.empty()) {
    Range r = stack.back();
    stack.pop_back();
    if (r.hi < r.lo) continue;
    int mid = r.lo + (r.hi - r.lo) / 2;
    m[mid] = mid;
    stack.push_back({mid + 1, r.hi});
    stack.push_back({r.lo, mid - 1});
  }
  int probe = n >= 7777 ? 7777 : n;
  auto it = m.find(probe);
  std::printf("%zu\n", m.size() + (it == m.end() ? 0 : it->second));
  return 0;
}
