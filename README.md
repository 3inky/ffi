<img width="851" height="106" alt="screenshot of ffi" src="https://github.com/user-attachments/assets/42c94317-4d06-4254-80cc-4e53fd51fe41" />

# ffi

**ffi** is a high-performance, cross-platform file search utility written in C.  
It is designed to work efficiently on **Windows**, **Linux**, and **macOS**, using multi-threading to maximize search speed.

## Features

- Cross-platform compatibility (Windows, Linux, macOS)
- Multi-threaded search for maximum performance
- Recursive directory search
- Search by file name or path
- Requires administrator/root privileges for protected directories
- Written in C for speed and low-level access
- Easy to compile with `gcc`, `clang`, or `msvc`

## Usage

```

ffi -p /path/to/search -fn filename_pattern

```

### Arguments:

- `-p`, `--path` : Path to start the search (recursive search included)
- `-fn`, `--file-name` : File name or pattern to search
- `-h`, `--help` : Show help message

Example:
```
ffi -p /home/user/Documents -fn "*.txt"
```

## Compilation

### Linux / macOS
```bash
mkdir build && cd build
cmake ..
cmake --build . -j4
```

### Windows (MSVC)

```powershell
mkdir build; cd build
cmake .. -G "Visual Studio 17 2022"
cmake --build . --config Release
```

## Prebuilt Binaries

Prebuilt binaries for supported platforms are available on the [GitHub Releases](https://github.com/yayydev/ffi/releases) page.
Download the appropriate binary for your operating system and extract it to use without compiling.

## Requirements

* C compiler (`gcc`, `clang`, or `MSVC`)
* CMake >= 3.15
* POSIX threads (`pthread`) support for Linux/macOS
* Administrator/root privileges for protected directories

## License

This project is licensed under the GPL license.
