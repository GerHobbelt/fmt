#include "fmt/format.h"


#if defined(BUILD_MONOLITHIC)
#define main      fmt_test_find_package_main
#endif

int main(int argc, char** argv) {
  for (int i = 0; i < argc; ++i) fmt::print("{}: {}\n", i, argv[i]);
  return 0;
}
