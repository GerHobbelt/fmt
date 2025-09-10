#include <iostream>
#include <string>

extern std::string foo();

#if defined(BUILD_MONOLITHIC)
#define main      fmt_test_static_export_main
#endif

int main(void) {
  std::cout << foo() << std::endl;
  return 0;
}
