import os
import subprocess
from pathlib import Path
from setuptools import setup
from setuptools.extension import Extension

ROOT = Path(__file__).parent.parent.absolute()

def find_libfhk():
    path = str(ROOT / "libfhkpy.a")
    if not os.path.isfile(path):
        raise RuntimeError(f"fhk library not found (looking for: {path}; try running make libfhkpy.a)")
    return [
        "-Wl,--whole-archive",
        path,
        "-Wl,--no-whole-archive"
    ]

def find_libluajit():
    # do we have a local one?
    path = str(ROOT / "LuaJIT" / "src" / "libluajit.a")
    if os.path.isfile(path):
        return [path]
    # pkg-config?
    lib = (
        subprocess.run("pkg-config --libs luajit", shell=True, capture_output=True)
        .stdout
        .decode("utf8")
        .strip()
    )
    if lib:
        return [lib]
    raise RuntimeError(f"no luajit found (pkg-config or local in {path})")

ctypes_ext = Extension(
    "fhk._ctypes",
    sources = [],
    extra_link_args = [*find_libfhk(), *find_libluajit()],
)

setup(
    name = "fhk",
    version = "0.0.1",
    packages = ["fhk"],
    ext_modules = [ctypes_ext]
)
