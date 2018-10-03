#include <fmt/color.h>
#include <fmt/ostream.h>
#include <iomanip>
#include <support.h>

template <typename F>
static void forSomeColors(F func) {
	auto primary = [](unsigned color) -> uint8_t { return (color & 0x3) * 0x40 + 0x30; };

	for (unsigned color = 0; color < (1 << 6); ++color) {
		const uint8_t r = primary(color >> 4);
		const uint8_t g = primary(color >> 2);
		const uint8_t b = primary(color >> 0);
		const fmt::rgb Background{ r, g, b };
		const double luminosity = 0.21 * r + 0.72 * g + 0.07 * b;
		const fmt::rgb Foreground = luminosity > 150 ? fmt::color::black : fmt::color::white;
		func(Foreground, Background);
	}
}

#if 1

static void simple() {
	forSomeColors([](fmt::rgb Foreground, fmt::rgb Background) {
		fmt::print(fmt::fg(Foreground) | fmt::bg(Background), L" {:02x}{:02x}{:02x} ", Background.r, Background.g, Background.b);
	});
	fmt::print(L"\n\n");
}

struct rgb_c : fmt::rgb {
	rgb_c(fmt::rgb color) : fmt::rgb(color) {}
};

template <typename Char>
struct fmt::formatter<rgb_c, Char> : fmt::formatter<uint8_t, Char> {
	using base = fmt::formatter<uint8_t, Char>;

	template <typename FormatContext>
	auto format(const rgb_c & color, FormatContext &ctx) {
		base::format(color.r, ctx);
		base::format(color.g, ctx);
		return base::format(color.b, ctx);
	}
};

static void custom() {
	forSomeColors([](rgb_c Foreground, rgb_c Background) {
		fmt::print(fmt::fg(Foreground) | fmt::bg(Background), L" {:02x} ", Background);
	});
	fmt::print(L"\n\n");
}

struct rgb_hc : fmt::rgb {
	rgb_hc(fmt::rgb color) : fmt::rgb(color) {}
};

template <typename Char>
struct fmt::formatter<rgb_hc, Char> : fmt::formatter<uint8_t, Char> {
	using base = fmt::formatter<uint8_t, Char>;

	template <typename FormatContext>
	auto format(const rgb_hc & color, FormatContext &ctx) {
		auto it = ctx.out();
		it = static_cast<Char>('(');
		it = base::format(color.r, ctx);
		it = static_cast<Char>(',');
		it = base::format(color.g, ctx);
		it = static_cast<Char>(',');
		it = base::format(color.b, ctx);
		it = static_cast<Char>(')');
		return it;
	}
};

static void custom_hardcoded() {
	forSomeColors([](rgb_hc Foreground, rgb_hc Background) {
		fmt::print(fmt::fg(Foreground) | fmt::bg(Background), L" {:3d}  ", Background);
	});
	fmt::print(L"\n\n");
}

struct rgb_fc : fmt::rgb {
	rgb_fc(fmt::rgb color) : fmt::rgb(color) {}
};

template <typename Char>
struct fmt::formatter<rgb_fc, Char> : fmt::formatter<uint8_t, Char> {
	using base = fmt::formatter<uint8_t, Char>;

	Char delimiter = {};
	bool isHex = false;
	bool isAlt = false;

    static constexpr bool isArgId(Char ch) {
		return ((ch >= '0') & (ch <= '9')) | ((ch >= 'a') & (ch <= 'z')) | ((ch >= 'A') & (ch <= 'Z')) | (ch == '_');
	};

	template <typename ParseContext>
	auto parse(ParseContext &ctx) {
		bool inBraces = false;
		unsigned pos = 0;
		unsigned prefix = 0;
		Char previous = {};
		for (auto ch : ctx) {
			if (inBraces) {
				if (ch == '}')
					inBraces = false;
				if (pos < 4) {
					if (ch == '}') {
						inBraces = false;
						if ((!isAlt & !delimiter & (pos == 1)) | (isAlt & (pos == 2)) | (delimiter & (pos == 3)))
							prefix = pos + 1;
					} else if ((pos == 1) & (ch == '#')) {
						isAlt = true;
					} else if (pos == 2) {
						if (isAlt | (previous == ':')) {
							delimiter = ch;
						} else if (!isArgId(previous)) {
							ctx.on_error("invalid prefix: first character must be ':' or '#'");
						}
					} else if (pos == 3) {
						ctx.on_error("invalid prefix: missing closing '}'");
					}
				}
			} else {
				if (ch == '{') {
					inBraces = true;
				} else if (ch == '}') {
					isHex = (previous == 'x') | (previous == 'X');
					break;
				}
			}
			++pos;
			previous = ch;
		}
		ctx.advance_to(ctx.begin() + prefix);
		return base::parse(ctx);
	}

	template <typename FormatContext>
	auto format(const rgb_fc & color, FormatContext &ctx) {
		auto it = ctx.out();
		if (isAlt) it = isHex ? Char{ '#' } : Char{ '(' };
		it = base::format(color.r, ctx);
		if (delimiter) it = delimiter;
		it = base::format(color.g, ctx);
		if (delimiter) it = delimiter;
		it = base::format(color.b, ctx);
		if (isAlt && !isHex) it = Char{ ')' };
		return it;
	}
};

static void custom_fancy() {
	forSomeColors([](rgb_fc Foreground, rgb_fc Background) {
		fmt::print(fmt::fg(Foreground) | fmt::bg(Background), L" {0:{#}02X}  ", Background);
	});
	fmt::print(L"\n\n");
}

#if 0
struct rgb_os : fmt::rgb {
	rgb_os(fmt::rgb color) noexcept : fmt::rgb(color) {}
};


template <typename Char>
std::basic_ostream<Char> & operator<<(std::basic_ostream<Char> & os, const rgb_os & color) {
	return os << Char{ '(' } << std::setw(3) << color.r
	          << Char{ ',' } << std::setw(3) << color.g
	          << Char{ ',' } << std::setw(3) << color.b
	          << Char{ ')' };
}

static void custom_ostream() {
	forSomeColors([](rgb_os Foreground, rgb_os Background) {
		fmt::print(Foreground, Background, L" {}  ", Background);
	});
	fmt::print(L"\n\n");
}
#endif
int main() {
	setupWideConsole();

	simple();
	custom();
	custom_hardcoded();
	custom_fancy();
//	custom_ostream();
}

#else

template <typename Char>
std::basic_ostream<Char> & operator<<(std::basic_ostream<Char> & os, const fmt::rgb &) {
	return os;
}

using TIE_BREAKER = void*;

template <typename Char>
struct fmt::formatter<fmt::rgb, Char, TIE_BREAKER> : fmt::formatter<uint8_t, Char> {
	using base = fmt::formatter<uint8_t, Char>;

	template <typename FormatContext>
	auto format(const fmt::rgb & color, FormatContext &ctx) {
		base::format(color.r, ctx);
		base::format(color.g, ctx);
		return base::format(color.b, ctx);
	}
};

static void custom_multiple_formatters() {
	forSomeColors([](fmt::rgb Foreground, fmt::rgb Background) {
		fmt::print(Foreground, Background, L" {}  ", Background);
	});
	fmt::print(L"\n\n");
}

int main() {
	setupWideConsole();

	custom_multiple_formatters();
}

#endif
