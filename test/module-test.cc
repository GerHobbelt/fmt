// Formatting library for C++ - module tests
//
// Copyright (c) 2012 - present, Victor Zverovich
// All rights reserved.
//
// For the license information refer to format.h.
//
// Copyright (c) 2021 - present, Daniela Engert
// All Rights Reserved
// {fmt} module.

import fmt;

// check for macros leaking from BMI
static bool macro_leaked = 
#if defined(FMT_CORE_H_) || defined(FMT_FORMAT_H)
  true;
#else
  false;
#endif

#include "gtest/gtest.h"

// an implicitly exported namespace must be visible [module.interface]/2.2
TEST(module_test, namespace) {
  using namespace fmt;
  ASSERT_TRUE(true);
}

// macros must not be imported from a *named* module  [cpp.import]/5.1
TEST(module_test, macros) {
#if defined(FMT_HIDE_MODULE_BUGS) && \
  defined(_MSC_FULL_VER) && _MSC_FULL_VER <= 192930035
// bug in msvc 16.10-pre3:
// include-guard macros leak from BMI
// and even worse: they cannot be #undef-ined
  macro_leaked = false;
#endif
  EXPECT_FALSE(macro_leaked);
}

TEST(module_test, to_string) {
  EXPECT_EQ("42", fmt::to_string(42));
  EXPECT_EQ("42", fmt::to_string(42u));
  EXPECT_EQ("42", fmt::to_string(short{42}));
  EXPECT_EQ("42", fmt::to_string(unsigned short{42u}));
  EXPECT_EQ("42", fmt::to_string(42l));
  EXPECT_EQ("42", fmt::to_string(42ul));
#if 0 // enable this to see msvc ICE
  EXPECT_EQ("42", fmt::to_string(42.0));
  EXPECT_EQ("42", fmt::to_string(42.0f));
#endif
  EXPECT_EQ("42", fmt::to_string("42"));
  EXPECT_EQ("a", fmt::to_string('a'));
}

#if 0 // enable this to see msvc ICE
TEST(module_test, string_view) {
  fmt::string_view nsv("fmt");
  EXPECT_EQ("fmt", nsv);
  EXPECT_TRUE(fmt::string_view("fmt") == nsv);

  fmt::wstring_view wsv(L"fmt");
  EXPECT_EQ(L"fmt", wsv);
  EXPECT_TRUE(fmt::wstring_view(L"fmt") == wsv);
}
#endif
