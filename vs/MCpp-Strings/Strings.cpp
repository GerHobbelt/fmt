#include <fmt/format.h>
#include <string>
#include <QtCore/QString>
#include <atlstr.h>

FMT_BEGIN_NAMESPACE
FMT_END_NAMESPACE

template <typename Char>
struct String {
	String(const Char * S) : S_(S) {}
	~String() = default;
	const Char * data() const FMT_NOEXCEPT { return S_.data(); }
	std::size_t length() const FMT_NOEXCEPT { return S_.size(); }
private:
	std::basic_string<Char> S_;
};

using wString = String<wchar_t>;

template <typename Char>
struct MyString : std::basic_string<Char> {
	MyString(const std::basic_string<Char> &S) : std::basic_string<Char>(S) {}
};

template <typename Char>
struct StringProxy {
	StringProxy(const Char * S) : S_(S) {}
	~StringProxy() = default;
	MyString<Char> str() const FMT_NOEXCEPT { return S_; }
private:
	std::basic_string<Char> S_;
};

using wStringProxy = StringProxy<wchar_t>;

struct dummy{};

template <typename Char>
static fmt::basic_string_view<Char> to_string_view(const String<Char> &S) FMT_NOEXCEPT {
	return { S.data(), S.length() };
}

template <typename Char>
static void to_string_view(const StringProxy<Char> &S) FMT_NOEXCEPT {
	return { S.data(), S.length() };
}

static fmt::basic_string_view<wchar_t> to_string_view(const QString &S) FMT_NOEXCEPT {
	return { reinterpret_cast<const wchar_t *>(S.utf16()), static_cast<std::size_t>(S.length()) };
}

namespace ATL {
template <typename Char>
static fmt::basic_string_view<Char> to_string_view(const CStringT<Char, StrTraitATL<Char, ChTraitsCRT<Char>>> &S) FMT_NOEXCEPT {
	return { static_cast<const Char *>(S), static_cast<std::size_t>(S.GetLength()) };
}
}

using afr = fmt::arg_formatter<fmt::back_insert_range<fmt::internal::buffer<char>>>;

FMT_BEGIN_NAMESPACE
namespace internal {
#if 1
static_assert(is_string<wString>::value, "");
static_assert(is_string<QString>::value, "");
static_assert(is_string<CString>::value, "");
static_assert(is_string<CStringA>::value, "");
static_assert(is_string<CStringW>::value, "");
static_assert(!is_string<dummy>::value, "");
static_assert(is_string<fmt::string_view>::value, "");
static_assert(!is_string<afr>::value, "");
#endif
} // internal
FMT_END_NAMESPACE

int main() {
#if 1
	const auto & w = wString(L"\n\n"); (void)w;
	std::wstring Result = fmt::format(wString(L"{}"), std::wstring(L"42"));
	Result = fmt::format(wString(L"{}{}"), wString(L"42"), wString(L"43"));

	const auto wq = QString("{}"); (void)wq;
	Result = fmt::format(QString("{}"), QString("© Grüße aus Nürnberg"));
//must fail!	std::string sResult = fmt::format("{}", QString("© Grüße aus Nürnberg"));

	Result.clear();
#endif
}
