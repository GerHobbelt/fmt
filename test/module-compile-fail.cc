// Copyright (c) 2012 - present, Victor Zverovich
// All rights reserved.
//
// For the license information refer to format.h.
//
// Copyright (c) 2021 - present, Daniela Engert
// All Rights Reserved
// {fmt} module.

import fmt;

// the non-exported namespace 'detail' must be invisible [module.interface]/2
using namespace fmt::detail;

#if defined(FMT_HIDE_MODULE_BUGS) && \
  defined(_MSC_FULL_VER) && _MSC_FULL_VER <= 192930035
// bug in msvc 16.10-pre3:
// the namespace is visible even when it is neither
// implicitly nor explicitly exported
#  error namespace 'fmt::detail' is visible!
#endif

int main() {}
