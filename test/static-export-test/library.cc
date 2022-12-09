#include <fmt/compile.h>

#if defined(_MSC_VER)
#define __attribute__(a)
#endif

__attribute__((visibility("default"))) std::string foo() {
  return fmt::format(FMT_COMPILE("foo bar {}"), 4242);
}
