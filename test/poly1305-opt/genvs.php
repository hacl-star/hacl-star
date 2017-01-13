<?

function get_guid($name) {
	$hex = strtoupper(md5($name));
	return "{".substr($hex, 0, 8)."-".substr($hex, 8, 4)."-".substr($hex, 12, 4)."-".substr($hex, 16, 4)."-".substr($hex, 20, 12)."}";
}

function addln($str) {
	return $str."\xd\xa";
}

function echoln($str) {
	echo $str;
	echo "\n";
}

function fecho($f, $str) {
	fwrite($f, $str);
}

function fecholn($f, $str) {
	fwrite($f, $str);
	fwrite($f, "\xd\xa");
}

function quote($str) {
	return "\"{$str}\"";
}

function fixslash($str) {
	return str_replace("/", "\\", $str);
}

function my_file_get_contents($path) {
	if (!file_exists($path)) {
		echoln("unable to open {$path}!\n");
		exit(1);
	}
	return file_get_contents($path);
}

$crawl_ignore = array("asmopt.h"=>1, "asmopt_internal.h"=>1, "util_implementations.h"=>1);

function crawl(&$list, $dir, $grab, $recurse) {
	global $crawl_ignore;
	$dh = opendir($dir);
	if ($dh) {
		while (($file = readdir($dh)) !== false) {
			$path = $dir."/".$file;
			if (($file == ".") || ($file == "..") || isset($crawl_ignore[$file]))
				continue;
			if (is_dir($path)) {
				if ($recurse)
					crawl($list, $path, $grab, $recurse);
			} else {
				foreach($grab as $pat) {
					if (preg_match($pat, $file)) {
						$list[] = fixslash($path);
						break;
					}
				}
			}
		}
		closedir($dh);
	}
}

abstract class gen_vs {
	protected $name;
	protected $builds;
	protected $projects;
	protected $sln;
	protected $project_dir;
	protected $files;
	protected $include_dirs;

	public function gen_vs($name) {
		$this->name = strtolower($name);
		$this->projects = array();

		foreach(array("lib", "dll", "util") as $type) {
			$name = "{$this->name}_{$type}";
			$this->projects[$type] = array("name"=>$name, "guid"=>get_guid($name));
		}

		$this->include_dirs = array("./", "../app/include", "../app/extensions", "../framework/include", "../framework/driver", "../framework/driver/x86");
	}

	public function build_files() {
		$this->files = array("driver"=>array(), "ext"=>array(), "util"=>array(), "shared"=>array(), "include"=>array());
		crawl($this->files["driver"], "framework/driver", array("!\.c$!", "!\.h$!", "!\.inc$!"), false);
		crawl($this->files["driver"], "framework/driver/x86", array("!\.c$!", "!\.S$!", "!\.h$!", "!\.inc$!"), false);
		crawl($this->files["ext"], "app/extensions", array("!\.c$!", "!\.S$!", "!\.inc$!", "!\.h$!"), true);
		crawl($this->files["include"], "app/include", array("!\.h$!"), false);
		crawl($this->files["include"], "framework/include", array("!\.h$!"), false);
		crawl($this->files["shared"], "framework", array("!main_shared\.c$!"), false);
		crawl($this->files["util"], "framework", array("!main_util\.c$!", "!fuzz\.c$!", "!bench\.c$!"), true);

		$this->projects["lib"]["files"] = array("driver", "ext", "include");
		$this->projects["dll"]["files"] = array("driver", "ext", "include", "shared");
		$this->projects["util"]["files"] = array("driver", "ext", "include", "util");
	}

	public function write_file($name, $str) {
		$in = array("%%name", "%%NAME", "%%projectdir");
		$out = array($this->name, strtoupper($this->name), $this->project_dir);
		$name = str_replace($in, $out, $name);
		$str = str_replace($in, $out, $str);
		$f = fopen("{$name}", "w+");
		chmod("{$name}", 0755);
		fwrite($f, $str);
		fclose($f);
	}

	public abstract function make();
};


/*
	vs 2010 'tricks'

	allow a files with the same name, but different paths, to be compiled correctly and not in to a flat directory: set
	ObjectFileName path to "$(IntDir)dummy\\%(RelativeDir)/", dummy eats the ../ we used to escape the vs2010 dir.


*/

class vs2010 extends gen_vs {
	protected $fileinfo;

	protected $toolset;
	protected $toolsversion;
	protected $fileformatversion;
	protected $vsversion;

	public function vs2010($name) {
		parent::gen_vs($name);

		$this->sln = "{$this->name}.sln";

		foreach($this->projects as $handle=>&$info)
			$info["vcxproj"] = "{$info['name']}.vcxproj";

		$this->builds = array(
			"Debug|x86-32bit"=>"Debug|Win32",
			"Debug|amd64"=>"Debug|x64",
			"Release|x86-32bit"=>"Release|Win32",
			"Release|amd64"=>"Release|x64"
		);

		$this->project_dir = "vs2010";
		$this->toolset = "v100";
		$this->fileformatversion = "11.00";
		$this->vsversion = "# Visual Studio 2010";
		$this->toolsversion = "4.0";
	}

	function make_sln() {
		$f = fopen("{$this->project_dir}/".$this->sln, "w+");
		fecho($f,
			addln("Microsoft Visual Studio Solution File, Format Version {$this->fileformatversion}").
			addln("{$this->vsversion}")
		);

		foreach($this->projects as $handle=>$info) {
			fecho($f,
				addln("Project(\"{8BC9CEB8-8B4A-11D0-8D11-00A0C91BC942}\") = ".quote($info["name"]).", ".quote($info["vcxproj"]).", ".quote($info["guid"])).
				addln("EndProject")
			);
		}

		fecholn($f, "Global");
			fecholn($f, "	GlobalSection(SolutionConfigurationPlatforms) = preSolution");
			foreach($this->builds as $label=>$build)
				fecholn($f, "		{$label} = {$label}");
			fecholn($f, "	EndGlobalSection");

			fecholn($f, "	GlobalSection(ProjectConfigurationPlatforms) = postSolution");
			foreach($this->projects as $handle=>$info) {
				foreach($this->builds as $label=>$build) {
					fecho($f,
						addln("		{$info['guid']}.{$label}.ActiveCfg = {$build}").
						addln("		{$info['guid']}.{$label}.Build.0 = {$build}")
					);
				}
			}
			fecholn($f, "	EndGlobalSection");

			fecho($f,
				addln("	GlobalSection(SolutionProperties) = preSolution").
				addln("		HideSolutionNode = FALSE").
				addln("	EndGlobalSection")
			);
		fecholn($f, "EndGlobal");
		fclose($f);
	}

	public function make_vcxproj_filters() {
		foreach($this->projects as $handle=>$info) {
			$f = fopen("{$this->project_dir}/".$info["vcxproj"].".filters", "w+");

			fecholn($f,
				"<?xml version=\"1.0\" encoding=\"utf-8\"?>".
				"<Project ToolsVersion=".quote($this->toolsversion)." xmlns=\"http://schemas.microsoft.com/developer/msbuild/2003\">"
			);

			/* list of filters we'll be using */
			fecho($f,
				"<ItemGroup>".
				"<Filter Include=\"Source\"></Filter>"
			);

			$seen = array();
			foreach($info["files"] as $handle) {
				foreach($this->files[$handle] as $path) {
					while (1) {
						$chop_directory = preg_replace("!^(.*)\\\\.*$!", "$1", $path);
						if ($chop_directory === $path)
							break;
						$seen[$chop_directory] = 1;
						$path = $chop_directory;
					}
				}
			}

			foreach($seen as $basepath=>$dummy)
				fecho($f, "<Filter Include=\"Source\\{$basepath}\"></Filter>");
			fecholn($f, "</ItemGroup>");
			/* list of filters we'll be using */

			/* list of files with their filters */
			foreach($info["files"] as $handle) {
				fecho($f, "<ItemGroup>");
				foreach($this->files[$handle] as $path) {
					$type = $this->fileinfo[$path]["type"];
					$folder = $this->fileinfo[$path]["basepath"];
					fecho($f, "<{$type} Include=\"..\\{$path}\"><Filter>Source\\{$folder}</Filter></{$type}>");
				}
				fecholn($f, "</ItemGroup>");
			}
			/* list of files with their filters */

			fecholn($f, "</Project>");

			fclose($f);
		}
	}

	public function make_vcxproj() {
		foreach($this->projects as $handle=>$info) {
			$f = fopen("{$this->project_dir}/".$info["vcxproj"], "w+");

			fecholn($f,
				"<?xml version=\"1.0\" encoding=\"utf-8\"?>".
				"<Project DefaultTargets=\"Build\" ToolsVersion=".quote($this->toolsversion)." xmlns=\"http://schemas.microsoft.com/developer/msbuild/2003\">"
			);

			/* build configurations */
			fecholn($f, "<ItemGroup Label=\"ProjectConfigurations\">");
			foreach($this->builds as $build) {
				$fields = explode("|", $build);
				fecholn($f,
					"<ProjectConfiguration Include=".quote($build).">".
					"<Configuration>{$fields[0]}</Configuration>".
					"<Platform>{$fields[1]}</Platform>".
					"</ProjectConfiguration>"
				);
			}
			fecholn($f, "</ItemGroup>");
			/* build configurations */


			/* properties for this project */
			fecholn($f,
				"<PropertyGroup Label=\"Globals\">".
				"<ProjectGuid>{$info['guid']}</ProjectGuid>".
				"<Keyword>Win32Proj</Keyword>".
				"<RootNamespace>{$this->name}</RootNamespace>".
				"<PlatformToolset>{$this->toolset}</PlatformToolset>".
				"</PropertyGroup>"
			);

			/* some project configuration options */
			fecholn($f, "<Import Project=\"$(VCTargetsPath)\Microsoft.Cpp.Default.props\" />");
			foreach($this->builds as $build) {
				$fields = explode("|", $build);
				$configurationmap = array("lib"=>"StaticLibrary", "dll"=>"DynamicLibrary", "util"=>"Application");
				$debuglibmap = array("Release"=>"false", "Debug"=>"true");
				fecholn($f,
					"<PropertyGroup Condition=\"'$(Configuration)|$(Platform)'=='{$build}'\" Label=\"Configuration\">".
					"<ConfigurationType>{$configurationmap[$handle]}</ConfigurationType>".
					"<CharacterSet>MultiByte</CharacterSet>".
					"<UseDebugLibraries>{$debuglibmap[$fields[0]]}</UseDebugLibraries>".
					"</PropertyGroup>"
				);
			}
			/* some project configuration options */

			fecholn($f, "<Import Project=\"$(VCTargetsPath)\Microsoft.Cpp.props\" />");

			fecholn($f,
				"<ImportGroup Label=\"PropertySheets\">".
				"<Import Project=\"$(UserRootDir)\Microsoft.Cpp.$(Platform).user.props\" Condition=\"exists('$(UserRootDir)\Microsoft.Cpp.$(Platform).user.props')\" Label=\"LocalAppDataPlatform\" />".
				"</ImportGroup>"
			);

			fecholn($f, "<PropertyGroup Label=\"UserMacros\" />");

			/* target and directories */
			foreach($this->builds as $label=>$build) {
				$fields = explode("|", $label);
				$target_name = $this->name;
				$target_ext = ($handle == "util") ? "exe" : $handle;
				fecholn($f,
					"<PropertyGroup Condition=\"'$(Configuration)|$(Platform)'=='{$build}'\">".
					"<OutDir>$(SolutionDir)..\\bin\\{$fields[0]}\\{$fields[1]}\\</OutDir>".
					"<IntDir>$(SolutionDir)..\\build\\{$handle}\\{$fields[0]}\\{$fields[1]}\\</IntDir>".
					"<TargetName>{$target_name}</TargetName>".
					"<TargetExt>.{$target_ext}</TargetExt>".
					"</PropertyGroup>"
				);
			}
			/* target and directories */


			/* compiler and linker */
			$settingsmap = array(
				"Optimization"=>array("Release"=>"MaxSpeed", "Debug"=>"Disabled"),
				"IntrinsicFunctions"=>array("Release"=>"true", "Debug"=>"false"),
				"InlineFunctionExpansion"=>array("Release"=>"AnySuitable", "Debug"=>"Disabled"),
				"FavorSizeOrSpeed"=>array("Release"=>"Speed", "Debug"=>"Neither"),
				"BufferSecurityCheck"=>array("Release"=>"false", "Debug"=>"true"),
				"EnableCOMDATFolding"=>array("Release"=>"true", "Debug"=>"false"),
				"OptimizeReferences"=>array("Release"=>"true", "Debug"=>"false"),
				"SubSystem"=>array("lib"=>"Windows", "dll"=>"Windows", "util"=>"Console"),
				"PreprocessorDefinitions"=>array("lib"=>"", "dll"=>"BUILDING_DLL;LIB_PUBLIC=__declspec(dllexport)", "util"=>"UTILITIES"),
			);

			$includes = "";
			foreach($this->include_dirs as $dir)
				$includes .= str_replace("/", "\\", $dir).";";

			foreach($this->builds as $build) {
				$fields = explode("|", $build);
				fecholn($f, "<ItemDefinitionGroup Condition=\"'$(Configuration)|$(Platform)'=='{$build}'\">");
				/* compiler */
				fecholn($f,
					"<ClCompile>".
					/* static options */
					"<PrecompiledHeader />".
					"<WarningLevel>Level4</WarningLevel>".
					"<WholeProgramOptimization>false</WholeProgramOptimization>".
					"<AdditionalIncludeDirectories>{$includes}</AdditionalIncludeDirectories>".
					"<ObjectFileName>$(IntDir)dummy\\%(RelativeDir)/</ObjectFileName>".
					/* custom options */
					"<BufferSecurityCheck>{$settingsmap['BufferSecurityCheck'][$fields[0]]}</BufferSecurityCheck>".
					"<Optimization>{$settingsmap['Optimization'][$fields[0]]}</Optimization>".
					"<IntrinsicFunctions>{$settingsmap['IntrinsicFunctions'][$fields[0]]}</IntrinsicFunctions>".
					"<InlineFunctionExpansion>{$settingsmap['InlineFunctionExpansion'][$fields[0]]}</InlineFunctionExpansion>".
					"<FavorSizeOrSpeed>{$settingsmap['FavorSizeOrSpeed'][$fields[0]]}</FavorSizeOrSpeed>".
					"<BufferSecurityCheck>{$settingsmap['BufferSecurityCheck'][$fields[0]]}</BufferSecurityCheck>".
					"<PreprocessorDefinitions>{$settingsmap['PreprocessorDefinitions'][$handle]};%(PreprocessorDefinitions)</PreprocessorDefinitions>".
					"</ClCompile>"
				);
				/* linker */

				switch ($handle) {
					case "lib":
						fecholn($f,
							"<Lib>".
							"<LinkTimeCodeGeneration>false</LinkTimeCodeGeneration>".
							"</Lib>"
						);
						break;

					case "dll":
					case "util":
						fecholn($f,
							"<Link>".
							"<GenerateDebugInformation>true</GenerateDebugInformation>".
							"<SubSystem>{$settingsmap['SubSystem'][$handle]}</SubSystem>".
							"<EnableCOMDATFolding>{$settingsmap['EnableCOMDATFolding'][$fields[0]]}</EnableCOMDATFolding>".
							"<OptimizeReferences>{$settingsmap['OptimizeReferences'][$fields[0]]}</OptimizeReferences>".
							"<ImportLibrary>$(OutDir){$this->name}.dll.lib</ImportLibrary>".
							"<ProgramDatabaseFile>$(TargetDir)$(TargetName)$(TargetExt).pdb</ProgramDatabaseFile>".
							"</Link>"
						);
						break;
				}
				fecholn($f, "</ItemDefinitionGroup>");
			}
			fecholn($f, "<Import Project=\"$(VCTargetsPath)\Microsoft.Cpp.targets\" />");
			/* compiler and linker */

			/* list of files */
			$yasm_includes = "";
			foreach($this->include_dirs as $dir)
				$yasm_includes .= "-I{$dir} ";

			foreach($info["files"] as $handle) {
				fecholn($f, "<ItemGroup>");
				foreach($this->files[$handle] as $path) {
					$type = $this->fileinfo[$path]["type"];
					$folder = $this->fileinfo[$path]["basepath"];
					$cleanpath = str_replace("../", "", $path);
					$basename = preg_replace("!(.*)\..*$!", "$1", $this->fileinfo[$path]["basename"]);
					if ($type == "CustomBuild") {
						fecholn($f,
							"<{$type} Include=\"..\\{$path}\">".
							"<Message>yasm [{$cleanpath}]</Message>".
							"<Command Condition=\"'$(Platform)'=='Win32'\">yasm -r nasm -p gas {$yasm_includes} -o $(IntDir)\\{$folder}\\{$basename}.obj -f win32 ..\\{$path}</Command>".
							"<Command Condition=\"'$(Platform)'=='x64'\">yasm -r nasm -p gas {$yasm_includes} -o $(IntDir)\\{$folder}\\{$basename}.obj -f win64 ..\\{$path}</Command>".
							"<Outputs>$(IntDir)\\{$folder}\\{$basename}.obj</Outputs>".
							"</{$type}>"
						);
					} else {
						fecholn($f, "<{$type} Include=\"..\\{$path}\"></{$type}>");
					}
				}
				fecholn($f, "</ItemGroup>");
			}
			/* list of files */

			fecholn($f, "</Project>");

			fclose($f);
		}
	}

	public function make_project() {
		$this->build_files();

		$this->fileinfo = array();
		foreach($this->files as $handle=>$list) {
			foreach($list as $path) {
				$basepath = preg_replace("!^(.*)\\\\.*$!", "$1", $path);
				$basename = preg_replace("!^.*\\\\(.*)$!", "$1", $path);
				$this->fileinfo[$path]["basepath"] = $basepath;
				$this->fileinfo[$path]["basename"] = $basename;

				$ext = preg_replace("!^.*\.(.*)$!", "$1", $path);
				switch ($ext) {
					case "c": $type = "ClCompile"; break;
					case "S": $type = "CustomBuild"; break;
					case "inc": $type = "ClHeader"; break;
					case "h": $type = "ClHeader"; break;
				}
				$this->fileinfo[$path]["type"] = $type;
			}
		}

		$this->make_vcxproj();
		$this->make_vcxproj_filters();
	}

	public function make() {
		if (!file_exists($this->project_dir))
			mkdir($this->project_dir, 0755);

		$this->make_sln();
		$this->make_project();
	}
}

class vs2012 extends vs2010 {
	public function vs2012($name) {
		parent::vs2010($name);

		$this->project_dir = "vs2012";
		$this->toolset = "v110";
		$this->fileformatversion = "12.00";
		$this->vsversion = "# Visual Studio 2012";
	}
}

class vs2013 extends vs2012 {
	public function vs2013($name) {
		parent::vs2012($name);

		$this->project_dir = "vs2013";
		$this->toolset = "v120";
		$this->fileformatversion = "12.00";
		$this->vsversion = "# Visual Studio 2013";
		$this->toolsversion = "12.0";
	}
}


class argument {
	var $set, $value;
}


class anyargument extends argument {
	function anyargument($flag) {
		global $argc, $argv;

		$this->set = false;

		for ($i = 1; $i < $argc; $i++) {
			if (!preg_match("!--".$flag."=(.*)!", $argv[$i], $m))
				continue;
			$this->value = $m[1];
			$this->set = true;
			return;
		}
	}
}

/* prefix an argument with a * to indicate default */
class multiargument extends anyargument {
	function multiargument($flag, $legal_values) {
		parent::anyargument($flag);

		$map = array();
		$default = false;
		foreach($legal_values as $value) {
			if (substr($value, 0, 1) == "*")
				$default = substr($value, 1);
			$map[$value] = true;
		}

		if (!$this->set) {
			if ($default === false) {
				usage("value not specified for --{$flag}!");
				exit(1);
			}
			$this->value = $default;
			return;
		}

		if (!isset($map[$this->value])) {
			usage("{$this->value} is not a valid parameter to --{$flag}!");
			exit(1);
		}
	}
}


class flag extends argument {
	function flag($flag) {
		global $argc, $argv;

		$this->set = false;

		$flag = "--{$flag}";
		for ($i = 1; $i < $argc; $i++) {
			if ($argv[$i] !== $flag)
				continue;
			$this->value = true;
			$this->set = true;
			return;
		}
	}
}

function usage($reason = "") {
		echoln("Usage: php genvs.php [flags]");
		echoln("Flags in parantheses are optional");
		echoln("");
		echoln("   --version=[vs2013,vs2012,vs2010]              which project type to generate");
		echoln("  (--disable-yasm)                               do not use yasm");
		echoln("");
		if ($reason)
			echoln($reason);
}

$help = new flag("help");
$disable_yasm = new flag("disable-yasm");
$version = new multiargument("version", array("vs2010", "vs2012", "vs2013"));


if ($help->set) {
	usage();
	exit(0);
}

$project_name = trim(my_file_get_contents("app/project.def"));

switch ($version->value) {
	case "vs2010": $sln = new vs2010($project_name); break;
	case "vs2012": $sln = new vs2012($project_name); break;
	case "vs2013": $sln = new vs2013($project_name); break;
}

$sln->make();


/* build framework/include/asmopt.h and framework/include/asmopt_internal.h */

if ($disable_yasm->set) {
	$yasm = "";
} else {
	$yasm = <<<EOS
/* Visual Studio with Yasm 1.2+ */
#define ARCH_X86
#define HAVE_AVX2
#define HAVE_AVX
#define HAVE_XOP
#define HAVE_SSE4_2
#define HAVE_SSE4_1
#define HAVE_SSSE3
#define HAVE_SSE3
#define HAVE_SSE2
#define HAVE_SSE
#define HAVE_MMX

EOS;
}

$asmopt_h = <<<EOS
#ifndef ASMOPT_H
#define ASMOPT_H

#include <stddef.h>

{$yasm}

#if (defined(_M_IX86))
	#define CPU_32BITS
#elif (defined(_M_X64))
	#define CPU_64BITS
#else
	#error This should never happen
#endif

#define HAVE_INT64
#define HAVE_INT32
#define HAVE_INT16
#define HAVE_INT8

#if (_MSC_VER < 1300)
	typedef signed __int64  int64_t; typedef unsigned __int64  uint64_t;
	typedef signed int      int32_t; typedef unsigned int      uint32_t;
	typedef signed short    int16_t; typedef unsigned short    uint16_t;
	typedef signed char      int8_t; typedef unsigned char      uint8_t;
#elif (_MSC_VER < 1600)
	typedef signed __int64  int64_t; typedef unsigned __int64  uint64_t;
	typedef signed __int32  int32_t; typedef unsigned __int32  uint32_t;
	typedef signed __int16  int16_t; typedef unsigned __int16  uint16_t;
	typedef signed __int8    int8_t; typedef unsigned __int8    uint8_t;
#else
	#include <stdint.h>
#endif

#endif /* ASMOPT_H */


EOS;


$asmopt_internal = <<<EOS
#ifndef ASMOPT_INTERNAL_H
#define ASMOPT_INTERNAL_H

#include "asmopt.h"

#define LOCAL_PREFIX3(a,b) a##_##b
#define LOCAL_PREFIX2(a,b) LOCAL_PREFIX3(a,b)
#define LOCAL_PREFIX(n) LOCAL_PREFIX2(PROJECT_NAME,n)
#define PROJECT_NAME %%name

/* yasm */
#if (0)
%define PROJECT_NAME %%name
#endif

#endif /* ASMOPT_INTERNAL_H */

EOS;

$sln->write_file("%%projectdir/asmopt.h", $asmopt_h);
$sln->write_file("%%projectdir/asmopt_internal.h", $asmopt_internal);



/* build framework/include/util_implemntations.h */

$impls = array();
crawl($impls, "app/include", array("!\.h$!"), false);

$impl_includes = "";
$impl_declares = "";
for ($i = 0; $i < count($impls); $i++) {
	$path = $impls[$i];
	$basename = preg_replace("!^.*\\\\(.*)\.h$!", "$1", $path);
	$impl_includes .= addln("#include \"{$basename}.h\"");
	$impl_declares .= ($i < (count($impls) - 1)) ? addln("\tmake_impl({$basename}),") : "\tmake_impl({$basename})";
}

$util_implementations = <<<EOS
{$impl_includes}

static const implementation_t implementations[] = {
{$impl_declares}
};

EOS;

$sln->write_file("%%projectdir/util_implementations.h", $util_implementations);

?>