from conans import ConanFile


class FMTConan(ConanFile):
    name = "fmt"
    version = "8.1.1"
    url = "https://github.com/Esri/fmt/tree/runtimecore"
    license = "https://github.com/Esri/fmt/blob/runtimecore/LICENSE"
    description = "{fmt} is an open-source formatting library providing a fast and safe alternative to C stdio and C++ iostreams."

    # RTC specific triple
    settings = "platform_architecture_target"

    def package(self):
        base = self.source_folder + "/"
        relative = "3rdparty/fmt/"

        # headers
        self.copy("*.h", src=base + "include", dst=relative + "include")

        # libraries
        output = "output/" + str(self.settings.platform_architecture_target) + "/staticlib"
        self.copy("*" + self.name + "*", src=base + "../../" + output, dst=output)
