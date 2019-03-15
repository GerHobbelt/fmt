module; // required by P1103 and C++20, illegal in Modules TS

// in case of Modules TS syntax, export might be defined as empty or an empty anonymous namespace
#ifdef module
#undef module
#endif // module

#include <cassert>
#include <cctype>
#include <cerrno>
#include <chrono>
#include <climits>
#include <cmath>
#include <cmath>
#include <cstdarg>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <ctime>
#include <algorithm>
#include <iterator>
#include <limits>
#include <locale>
#include <memory>
#include <ostream>
#include <sstream>
#include <stdexcept>
#include <string>
#include <type_traits>
#include <vector>

#define FMT_BUILDING_MODULE

export module fmt;

#include "fmt/core.h"
#include "fmt/format.h"
#include "fmt/locale.h"
#include "fmt/ostream.h"
#include "fmt/printf.h"
#include "fmt/chrono.h"
#include "fmt/prepare.h"
#include "fmt/ranges.h"
#include "fmt/color.h"
