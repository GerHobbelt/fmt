#pragma once
#include <type_traits>
#include <string>

struct tagRECT;
class QString;
class QRect;

namespace boost {
	template<typename charT, typename traits> class basic_string_ref;
	using string_ref  = basic_string_ref<char, std::char_traits<char>>;
	using wstring_ref = basic_string_ref<wchar_t, std::char_traits<wchar_t>>;

	template<typename charT, typename traits> class basic_string_view;
	using string_view = basic_string_view<char, std::char_traits<char>>;
	using wstring_view = basic_string_view<wchar_t, std::char_traits<wchar_t>>;
}

namespace gmhpt {
namespace detail {
template <typename T, typename U> struct require_type_impl {};
template <typename T> struct require_type_impl<T, T> { using type = bool; };
} // namespace detail

template <typename T, typename U>
using require_type = typename detail::require_type_impl<std::remove_cv_t<std::remove_reference_t<T>>, U>::type;

namespace QtHelper {
	template <class Q> inline Q to(const std::wstring & s) { return Q::fromStdWString(s); }
	template <class Q> inline Q to(const std::string & s)  { return Q::fromStdString(s);  }
	template <class Q, class R, require_type<R, boost::wstring_ref> = true>  inline Q to(R s) { return Q::fromWCharArray(s.data(), static_cast<int>(s.size())); }
	template <class Q, class R, require_type<R, boost::string_ref> = true>   inline Q to(R s) { return Q::fromAscii(s.data(), static_cast<int>(s.size()));        }
	template <class Q, class V, require_type<V, boost::wstring_view> = true> inline Q to(V s) { return Q::fromWCharArray(s.data(), static_cast<int>(s.size())); }
	template <class Q, class V, require_type<V, boost::string_view> = true>  inline Q to(V s) { return Q::fromAscii(s.data(), static_cast<int>(s.size())); }
	template <class Q> inline Q to(const char * s)    { return Q::fromAscii(s);      }
	template <class Q> inline Q to(const wchar_t * s) { return Q::fromWCharArray(s); }

	template <class Q, class R, require_type<R, tagRECT> = true> inline Q to(const R & r) { return Q(r.left, r.top, r.right - r.left, r.bottom - r.top); }
}
namespace wstringHelper {
	template <class W> inline W to(const std::string & s) {
		return s.empty() ? W() : W(reinterpret_cast<const unsigned char*>(&s.front()), reinterpret_cast<const unsigned char*>(&s.front() + s.size()));
	}
	template <class W, class R, require_type<R, QString> = true> inline W to(const R & s) { return s.toStdWString(); }
}
namespace wstring_refHelper {
	template <class W, class R, require_type<R, QString> = true> inline W to(const R & s) { return s.isEmpty() ? W() : W(reinterpret_cast<const wchar_t*>(s.utf16()), s.size()); }
	template <class W> inline W to(const std::wstring & s) { return s.empty() ? W() : W(s.data(), s.size()); }
}
namespace wstring_viewHelper {
	template <class W, class R, require_type<R, QString> = true> inline W to(const R & s) { return s.isEmpty() ? W() : W(reinterpret_cast<const wchar_t*>(s.utf16()), s.size()); }
	template <class W> inline W to(const std::wstring &s) { return s.empty() ? W() : W(s.data(), s.size()); }
}
namespace stringHelper {
	template <class S> inline S to(const std::wstring &w) { return S(w.begin(), w.end()); }
	template <class S, class R, require_type<R, QString> = true> inline S to(const R &s) { return s.toStdString(); }
}
namespace string_refHelper {
	template <class S> inline S to(const std::string &s) { return s.empty() ? S() : S(s.data(), s.size()); }
}
namespace string_viewHelper {
	template <class S> inline S to(const std::string &s) { return s.empty() ? S() : S(s.data(), s.size()); }
}
}

#define _Q(s)  ::gmhpt::QtHelper::to<QString>(s)
#define _W(s)  ::gmhpt::wstringHelper::to<std::wstring>(s)
#define _WR(s) ::gmhpt::wstring_refHelper::to<boost::wstring_ref>(s)
#define _WV(s) ::gmhpt::wstring_viewHelper::to<boost::wstring_view>(s)
#define _S(s)  ::gmhpt::stringHelper::to<std::string>(s)
#define _SR(s) ::gmhpt::string_refHelper::to<boost::string_ref>(s)
#define _SV(s) ::gmhpt::string_viewHelper::to<boost::string_ref>(s)
#define _QR(r) ::gmhpt::QtHelper::to<QRect>(r)
