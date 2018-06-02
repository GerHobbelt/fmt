// stdafx.h : include file for standard system include files,
// or project specific include files that are used frequently, but
// are changed infrequently

#pragma once

#pragma warning(disable:4512) // this is *never* an error!
#pragma warning(disable:4127) // constant conditional expressions are extremely common in C++

#define QT_DISABLE_DEPRECATED_BEFORE 0x040807

#include "targetver.h"

#define _USE_MATH_DEFINES		            // include definition of math constants like M_PI
#define WIN32_LEAN_AND_MEAN                 // Exclude rarely-used stuff from Windows headers
#define _ATL_CSTRING_EXPLICIT_CONSTRUCTORS  // some CString constructors will be explicit

#ifndef VC_EXTRALEAN
#define VC_EXTRALEAN                        // Exclude rarely-used stuff from Windows headers
#endif

#if defined(NDEBUG)                         // nur Release-Builds
#define BOOST_DISABLE_ASSERT 1
#if _MSC_VER < 1600
// Bevor VC10 waren Container und Iteratoren im Release-Build nicht sauber!
// O-Ton Microsoft: wir schämen uns für diesen Blödsinn und korrigieren das in VC10 gemäß Kundenwunsch
// Ab VC10 bedeutet Release wirklich frei von Debug-Code.
// Achtung: Änderung benötigt ein Recompile von allen Bibliotheken (Boost, etc. )!
#undef _SECURE_SCL
#define _SECURE_SCL 0
#endif
#endif

#pragma push_macro ("_SCL_SECURE_NO_DEPRECATE")
#if defined(_DEBUG)
#undef  _SCL_SECURE_NO_DEPRECATE
#define _SCL_SECURE_NO_DEPRECATE            // zähme Warnungen aus Microsoft Library bei Warnstufe 4
#endif

#include <boost/config.hpp>

#pragma pop_macro ("_SCL_SECURE_NO_DEPRECATE")

#if defined (_AFXDLL)
#include "stdafx_mfcatl.h"
#endif

#define NOMINMAX                            // no min / max macros, use type-safe templates instead

#ifdef _MSC_VER
// Achtung: dies sind C++ Keywords in compilerspezifischen Implementierungen und in C++11
// sobald implementiert, müssen diese #defines angepaßt werden!

#if _MSC_VER < 1600
// nullptr und nullptr_t, implementiert ab VC10
#include <nullptr.hpp>

// static_assert, implementiert ab VC10
#include <boost/static_assert.hpp>
#define static_assert(x)     BOOST_STATIC_ASSERT(x)
#define static_assert(x,msg) BOOST_STATIC_ASSERT(x,msg)
#endif

#if _MSC_VER < 1700
    // enum-Basistypen, definierbar ab VC11
    #pragma warning(disable: 4480)
// override, voll implementiert ab VC11
#pragma warning(disable: 4481)
// qualifizierte enum-Bezeichner, akzeptiert ab VC11
#pragma warning(disable: 4482)

// final, hat anderen Namen unter VC10
#ifndef final
#define final sealed
#endif
#endif

#if _MSC_VER < 1900
// noexcept, implementiert ab VC14
// siehe "Boost Exception Specification Rationale", "A Pragmatic Look at Exception Specifications"
#define noexcept throw()

// thread_local, implementiert ab VC14
#define thread_local _declspec(thread)

// constexpr, implementiert ab VC14
#define constexpr
#endif

// Achtung Ende
#endif // _MSC_VER defined

#ifndef NO_GMHPT_UNUSED
#  define _GMHPT_UNUSED_CONCAT(x,y) x##y
#  define _GMHPT_UNUSED_ASSERTE(x) _ASSERTE(x)
#  define UNUSED(x) (void)x
#  define UNUSED_OR_ASSERT(x,y) _GMHPT_UNUSED_ASSERTE(_GMHPT_UNUSED_CONCAT(x,y)); UNUSED(x)
#endif

#include "LibraryCustomizations.h"
