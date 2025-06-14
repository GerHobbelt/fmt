// Formatting library for C++
//
// Copyright (c) 2012 - 2016, Victor Zverovich
// All rights reserved.
//
// For the license information refer to format.h.

#ifdef AMALGAMATED_SOURCECODE

#ifdef __GNUC__
#pragma GCC visibility push(default)
#endif
#include "fmt/format-inl.h"

FMT_BEGIN_NAMESPACE
namespace detail {

#if FMT_USE_LOCALE
// DEPRECATED! locale_ref in the detail namespace
template FMT_API locale_ref::locale_ref(const std::locale& loc);
template FMT_API auto locale_ref::get<std::locale>() const -> std::locale;
#endif

// Explicit instantiations for char.

template FMT_API auto thousands_sep_impl(locale_ref)
    -> thousands_sep_result<char>;
template FMT_API auto decimal_point_impl(locale_ref) -> char;

// DEPRECATED!
template FMT_API void buffer<char>::append(const char*, const char*);

// DEPRECATED!
template FMT_API void vformat_to(buffer<char>&, string_view,
                                 typename vformat_args<>::type, locale_ref);

// Explicit instantiations for wchar_t.

template FMT_API auto thousands_sep_impl(locale_ref)
    -> thousands_sep_result<wchar_t>;
template FMT_API auto decimal_point_impl(locale_ref) -> wchar_t;

template FMT_API void buffer<wchar_t>::append(const wchar_t*, const wchar_t*);

}  // namespace detail
FMT_END_NAMESPACE

#endif // AMALGAMATED_SOURCECODE
