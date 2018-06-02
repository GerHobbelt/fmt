/* Template zur automatischen Erzeugung einer projektspezifischen Datei 'Version.h' im jeweiligen Projektverzeichnis
 *
 * 'Version.h' ist Ergebnis des Pre-Build-Steps
 * Die eigentliche Arbeit (Abfrage des SubVersion-Repository, Ersetzen der Platzhalter und Schreiben der Ausgabedatei)
 * wird von SubWCRev.exe aus der TortoiseSVN-Installation erledigt
 */
#define _QUOTER_(x) L#x

// Namen
#define PRODUCT_NAME L"{fmt} TestApps"
#define SHORT_PRODNM L"{fmt}"
#define COMPANY_NAME L"{fmt} contributors"
#define SHORTCOMPANY L"{fmt} contributors"
#define VENDORDOMAIN L"fmtlib.net"

// Copyright
#define COPYRIGHT_YEAR_FIRST 2012
#define COPYRIGHT_YEAR_LAST  $WCDATE=%Y$
#if COPYRIGHT_YEAR_FIRST==COPYRIGHT_YEAR_LAST
#define _COPYRIGHT_(yf,yl) _QUOTER_(yf)
#else
#define _COPYRIGHT_(yf,yl) _QUOTER_(yf) L"-" _QUOTER_(yl)
#endif
#define COPYRIGHT       L"© " _COPYRIGHT_(COPYRIGHT_YEAR_FIRST,COPYRIGHT_YEAR_LAST) L" " COMPANY_NAME L". Alle Rechte vorbehalten."
#define COPYRIGHTYEARS  _COPYRIGHT_(COPYRIGHT_YEAR_FIRST,COPYRIGHT_YEAR_LAST)

// Software Version
#ifndef VERSION_MAJOR
#define VERSION_MAJOR	5
#endif
#ifndef VERSION_MINOR
#define VERSION_MINOR	2
#endif
#ifndef VERSION_FIXES
#define VERSION_FIXES	1
#endif
#define VERSION_BUILD	$WCREV$
#define VERSION_BUILDID	$WCREV$

// Produkt Version
#define PRODUCT_MAJOR	5
#define PRODUCT_MINOR	2
#define PRODUCT_FIXES	1
#define PRODUCT_BUILD	0

#define _VERSION_(maj,min,fix,bld) _QUOTER_(maj) L"." _QUOTER_(min) L"." _QUOTER_(fix) L"." _QUOTER_(bld)
#define FULLVERSION _VERSION_(VERSION_MAJOR,VERSION_MINOR,VERSION_FIXES,VERSION_BUILDID)
#define PRODVERSION _VERSION_(PRODUCT_MAJOR,PRODUCT_MINOR,PRODUCT_FIXES,VERSION_BUILDID)

#define _SHRTVRSN_(maj,min) _QUOTER_(maj) L"." _QUOTER_(min)
#define SHORTVERSION _SHRTVRSN_(VERSION_MAJOR,VERSION_MINOR)
#define SHORTPRODVER _SHRTVRSN_(PRODUCT_MAJOR,PRODUCT_MINOR)

// Source Code Management System Info
#define SCM_URL      "$WCURL$"
#define SCM_REVISION "$WCREV$"
#define SCM_DATE     "$WCDATE=%d.%m.%Y$"
#define SCM_MODIFIED "$WCMODS?modifiziert:revisioniert$"
