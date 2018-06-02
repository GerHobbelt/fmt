#pragma once

#pragma warning (disable: 4505) // unreferenced local function has been removed (from CppUnitTest.h)

#ifndef RETURN_WIDE_STRING
# error "include CppUnitTest.h before this extension header"
#endif

#include <sstream>
#include <string>
#include <vector>
#include <system_error>
#include <eh.h>
#include <winerror.h>

//=============================================================================================================

// translate structured exception into c++ exceptions
// translation takes place in current scope only

struct _EXCEPTION_POINTERS;

namespace gmhpt { namespace SEH {

//--------------------------------------------------------------------------------------------------------------

struct Exception : public std::system_error {
	explicit Exception(unsigned Code) : std::system_error(Code, std::system_category()) {}
};

struct AccessViolation : public Exception {
	explicit AccessViolation(unsigned Code) : Exception(Code) {}
};

// turn Windows structured exceptions into C++ exceptions to be consumed by C++ facilities
struct ScopedTranslator {
	typedef void (__cdecl *pTranslator)(unsigned, _EXCEPTION_POINTERS*);
	explicit ScopedTranslator(pTranslator Translator) : previous(_set_se_translator (Translator)) {}
	ScopedTranslator() : ScopedTranslator(translate) {}
	~ScopedTranslator() { _set_se_translator (previous); }

private:
	ScopedTranslator(const ScopedTranslator &) = delete;
	ScopedTranslator& operator=(const ScopedTranslator&) = delete;

	pTranslator const previous;
	static void translate(unsigned int Code, _EXCEPTION_POINTERS*) {
		if (Code == (0xC0000000 | ERROR_ACCESS_DENIED))
			throw AccessViolation(Code);
		else
			throw Exception(Code);
	}
};

//--------------------------------------------------------------------------------------------------------------

}}

//=============================================================================================================

namespace Microsoft { namespace VisualStudio { namespace CppUnitTestFramework {

//--------------------------------------------------------------------------------------------------------------
// primary templates of Microsoft::VisualStudio::CppUnitTestFramework::ToString
// a specialization is required for each type used in any Assert::xyz method

template <typename T> static std::wstring ToString(const T&);
template <typename T> static std::wstring ToString(const T*);
template <typename T> static std::wstring ToString(T*);

//--------------------------------------------------------------------------------------------------------------
// additional specializations in addition to those supplied by Microsoft

template<> inline std::wstring ToString<unsigned short>(const unsigned short& t) {
	RETURN_WIDE_STRING(t);
}

template<> inline std::wstring ToString<std::error_code>(const std::error_code &ec) {
	RETURN_WIDE_STRING('{' << ec.category().name() << ':' << ec.value() << '}');
}

template<typename T> inline std::wstring ToString(const std::vector<T> &Vec) {
	std::wstringstream s_;
	s_ << L'{';
	for (const auto & Elem : Vec)
		s_ << Elem << L',';
	s_ << L'}';
	return s_.str();
}

}}}

//=============================================================================================================

