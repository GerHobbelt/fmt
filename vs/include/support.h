#pragma once

#include <io.h> // for _setmode
#include <fcntl.h> // for _O_U16TEXT
#include <Windows.h> // for *ConsoleMode

inline void switchToWide(FILE * Stream) {
	_setmode(_fileno(Stream), _O_U16TEXT); // switch Stream into wchar_t (UTF16) mode
}

inline void setupConsole() {
#if _MSC_VER >= 1900
	DWORD ConsoleMode;
	GetConsoleMode(GetStdHandle(STD_OUTPUT_HANDLE), &ConsoleMode);
	SetConsoleMode(GetStdHandle(STD_OUTPUT_HANDLE), ConsoleMode | ENABLE_VIRTUAL_TERMINAL_PROCESSING);
#endif
}

inline void setupWideConsole() {
	setupConsole();
	switchToWide(stdout);
}
