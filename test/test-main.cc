// Formatting library for C++ - test main function.
//
// Copyright (c) 2012 - present, Victor Zverovich
// All rights reserved.
//
// For the license information refer to format.h.

#include <cstdlib>

#include "gtest/gtest.h"

#ifdef _WIN32
#  include <windows.h>
#endif

#ifdef _MSC_VER
#  include <crtdbg.h>
#endif


#if !defined(MUDRAW_STANDALONE) && defined(BUILD_MONOLITHIC)
#define main(cnt, arr)      fmt_test_main(cnt, arr)
#endif

int main(int argc, const char** argv) {
#ifdef _WIN32
  // Don't display any error dialogs. This also suppresses message boxes
  // on assertion failures in MinGW where _set_error_mode/CrtSetReportMode
  // doesn't help.
  SetErrorMode(SEM_FAILCRITICALERRORS | SEM_NOGPFAULTERRORBOX |
               SEM_NOOPENFILEERRORBOX);
#endif
#ifdef _MSC_VER
  // Disable message boxes on assertion failures.
  _CrtSetReportMode(_CRT_ERROR, _CRTDBG_MODE_FILE | _CRTDBG_MODE_DEBUG);
  _CrtSetReportFile(_CRT_ERROR, _CRTDBG_FILE_STDERR);
  _CrtSetReportMode(_CRT_ASSERT, _CRTDBG_MODE_FILE | _CRTDBG_MODE_DEBUG);
  _CrtSetReportFile(_CRT_ASSERT, _CRTDBG_FILE_STDERR);
#endif
  try {
    testing::InitGoogleTest(&argc, argv);
    testing::FLAGS_gtest_death_test_style = "threadsafe";
    return RUN_ALL_TESTS();
  } catch (...) {
    // Catch all exceptions to make Coverity happy.
  }
  return EXIT_FAILURE;
}
