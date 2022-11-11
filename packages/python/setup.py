import os
import pathlib
import shlex
import shutil
import subprocess
import sysconfig
import setuptools.command.build_ext
from setuptools import Extension, setup

DIR         = pathlib.Path(__file__).parent.resolve()
ROOT        = DIR.parent.parent
MAKE        = "make"
MAKEFLAGS   = shlex.split(os.environ.get("FHK_PY_MAKEFLAGS", ""))
EXT_SUFFIX  = sysconfig.get_config_var("EXT_SUFFIX")

try:
    VERSION = os.fsdecode(subprocess.check_output(["git", "describe", "--abbrev=0"]))[1:]
except:
    VERSION = "unknown"

class BuildExtFhk(setuptools.command.build_ext.build_ext):

    def build_extension(self, ext):
        make = [MAKE, "-C", str(ROOT), "pyx", *MAKEFLAGS]
        print(f"-> Building fhk: {make}")
        subprocess.run(make, check=True)
        extname = f"fhk{EXT_SUFFIX}"
        path = self.get_ext_fullpath(ext.name)
        print(f"-> Copying extension: {extname} => {path}")
        pathlib.Path(path).parent.mkdir(parents=True, exist_ok=True)
        shutil.move(ROOT/extname, path)

setup(
    name = "fhk",
    version = VERSION,
    description = "Computational graph solver",
    url = "https://github.com/menu-hanke/fhk",
    ext_modules = [Extension("fhk", [])],
    packages = ["fhk"],
    package_data = { "fhk": ["*.pyi"] },
    cmdclass = { "build_ext": BuildExtFhk }
)
