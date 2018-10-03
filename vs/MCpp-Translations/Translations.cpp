#include <stdafx.h>

#include <fmt/format.h>
#include <libEnvironment/Environment.h>
#include <boost/locale/message.hpp>
#include <string>
#include <QtCore/QCoreApplication>
#include <QtCore/QString>
#include "Version.h"

#pragma warning(disable: 4505) // unreferenced local function has been removed

namespace loc = boost::locale;
using loc::translate;

/* ============================================================================================================ */

using std::string;
using std::wstring;
using boost::locale::wmessage;

/* ============================================================================================================ */

static fmt::basic_string_view<wchar_t> to_string_view(const QString &S) FMT_NOEXCEPT {
	return { reinterpret_cast<const wchar_t *>(S.utf16()), static_cast<std::size_t>(S.length()) };
}

namespace boost { namespace locale {

template <typename Char>
static fmt::basic_string_view<Char> to_string_view(const basic_message<Char> &M) FMT_NOEXCEPT {
	auto view = M.sv(); // initiates the actual translation process
	return { view.data(), view.size() };
}

}} // namespace boost::locale

FMT_BEGIN_NAMESPACE
namespace internal {
#if 1
static_assert(is_string<QString>::value, "");
static_assert(is_string<wmessage>::value, "");
#endif
} // internal
FMT_END_NAMESPACE

int main(int argc, char *argv[]) {
	QCoreApplication ThisApp(argc, argv);
	const string Language = gmhpt::getMostSpecificISO639Language();
	gmhpt::installTranslations(ThisApp, Language, PROJECT_NAME);

	wstring wDisclaimer = translate(L"© 2018 All rights reserved");
	wDisclaimer = fmt::format(translate(L"{:*^50} - Greetings from Nuremberg"), translate(L"© 2018 All rights reserved"));

	auto sDisclaimer = fmt::format(translate("{:*^50} - Greetings from Nuremberg"), translate(u8"© 2018 All rights reserved"));
	auto QDisclaimer = fmt::format(QObject::tr("{:*^50} - Greetings from Nuremberg"), QObject::tr("© 2018 All rights reserved"));
	wDisclaimer.clear();
	sDisclaimer.clear();
	QDisclaimer.clear();
}
