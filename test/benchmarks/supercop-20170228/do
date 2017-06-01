#!/bin/sh -e

# supercop/do
# D. J. Bernstein
# Public domain.

version=`cat version`
project=supercop
shorthostname=`hostname | sed 's/\..*//' | tr -cd '[a-z][A-Z][0-9]' | tr '[A-Z]' '[a-z]'`

top="`pwd`/bench/$shorthostname"
bin="$top/bin"
lib="$top/lib"
include="$top/include"
work="$top/work"

PATH="/usr/local/bin:$PATH"
PATH="/usr/sfw/bin:$PATH"
PATH="$bin:$PATH"
export PATH

LD_LIBRARY_PATH="/usr/local/lib/sparcv9:/usr/local/lib:$LD_LIBRARY_PATH"
LD_LIBRARY_PATH="/usr/sfw/lib/sparcv9:/usr/sfw/lib:$LD_LIBRARY_PATH"
export LD_LIBRARY_PATH

# and wacky MacOS X
DYLD_LIBRARY_PATH="/usr/local/lib/sparcv9:/usr/local/lib:$DYLD_LIBRARY_PATH"
DYLD_LIBRARY_PATH="/usr/sfw/lib/sparcv9:/usr/sfw/lib:$DYLD_LIBRARY_PATH"
export DYLD_LIBRARY_PATH

# and work around bug in GNU sort
LANG=C
export LANG

rm -rf "$top"
mkdir -p "$top"
mkdir -p "$bin"
mkdir -p "$lib"
mkdir -p "$include"

cp include/* "$include"

exec >"$top/log"
exec 2>&1
exec 5>"$top/data"
exec </dev/null

echo "=== `date` === starting"

echo "=== `date` === building machineinfo"
rm -rf "$work"
mkdir -p "$work"
cp -pr machineinfo/* "$work"
( cd "$work" && sh do )

echo "=== `date` === building scripts"
cp -p scripts/* "$bin"

echo "=== `date` === building okcompilers"
rm -rf "$work"
mkdir -p "$work"
cp -pr okcompilers/* "$work"
( cd "$work" && sh do )
cp -p "$work"/bin/* "$bin"

echo "=== `date` === building cpuid"
rm -rf "$work"
mkdir -p "$work"
cp -pr cpuid/* "$work"
( cd "$work" && sh do )
cp -pr "$work"/include/* "$include"

echo "=== `date` === building inttypes"
rm -rf "$work"
mkdir -p "$work"
cp -pr inttypes/* "$work"
( cd "$work" && sh do )
cp -pr "$work"/include/* "$include"

echo "=== `date` === building killafter"
rm -rf "$work"
mkdir -p "$work"
cp -pr killafter/* "$work"
( cd "$work" && sh do )
cp -p "$work"/bin/* "$bin"

echo "=== `date` === building sinceepoch"
rm -rf "$work"
mkdir -p "$work"
cp -pr sinceepoch/* "$work"
( cd "$work" && sh do )
cp -p "$work"/bin/* "$bin"

echo "=== `date` === building cpucycles"
rm -rf "$work"
mkdir -p "$work"
cp -pr cpucycles/* "$work"
( cd "$work" && sh do )
cp -pr "$work"/lib/* "$lib"
cp -pr "$work"/include/* "$include"

okabi \
| while read abi
do
  echo "=== `date` === building gmp for $abi"
  mkdir -p "$lib/$abi"
  mkdir -p "$include/$abi"
  okc-$abi | head -1 \
  | while read c copts
  do
    okcpp-$abi | head -1 \
    | while read cpp cppopts
    do
      for gmpabi in 64 32 2.0w 2.0n 1.0 o32 n32 aix64 mode64 mode32 standard
      do
	[ -s "$lib/$abi/libgmp.a" ] && continue
	echo "=== `date` === trying CC=$c CXX=$cpp CFLAGS=$copts CXXFLAGS=$cppopts ABI=$gmpabi"
	rm -rf "$work"
	mkdir -p "$work"
	cp -pr gmp-6.1.1/* "$work"
	( cd "$work" \
	  && ./configure --enable-cxx \
	     ABI="$gmpabi" \
	     CC="$c" CXX="$cpp" CFLAGS="$copts" CXXFLAGS="$cppopts" LDFLAGS="$copts" \
	  && make \
	  && make check \
	  && cp gmp.h gmpxx.h gmp-impl.h longlong.h \
	  config.h gmp-mparam.h fac_table.h fib_table.h mp_bases.h "$include/$abi" \
	  && ( ranlib ".libs/libgmp.a" || : ) \
	  && cp .libs/libgmp.a "$lib/$abi/libgmp.a" \
	  && chmod 644 "$lib/$abi/libgmp.a" \
	  && ( ranlib ".libs/libgmpxx.a" || : ) \
	  && ( cp .libs/libgmpxx.a "$lib/$abi/libgmpxx.a" || : ) \
	  && ( chmod 644 "$lib/$abi/libgmpxx.a" || : )
	) && break
      done
    done
  done
done

okabi \
| while read abi
do
  echo "=== `date` === building cryptopp for $abi"
  mkdir -p "$lib/$abi"
  mkdir -p "$include/$abi/cryptopp"
  okcpp-$abi | head -1 \
  | while read cpp cppopts
  do
    [ -s "$lib/$abi/libcryptopp.a" ] && continue
    echo "=== `date` === trying CXX=$cpp CXXFLAGS=$cppopts"
    rm -rf "$work"
    mkdir -p "$work"
    cp -pr cryptopp-562/* "$work"
    ( cd "$work" \
      && make CXX="$cpp" CXXFLAGS="-DNDEBUG $cppopts" LDFLAGS="$cppopts" \
      && cp libcryptopp.a "$lib/$abi/libcryptopp.a" \
      && cp *.h "$include/$abi/cryptopp/"
    ) && break
  done
done

okabi \
| while read abi
do
  rm -rf "$work"
  mkdir -p "$work"
  echo 'void crypto_'"$project"'_base(void) { ; }' > "$work/${project}_base.c"
  okc-$abi \
  | while read compiler
  do
    ( cd "$work" && $compiler -c ${project}_base.c ) && break
  done
  okar-$abi cr "$lib/$abi/lib${project}.a" "$work/${project}_base.o"
  ( ranlib "$lib/$abi/lib${project}.a" || exit 0 )
done

# loop over operations
cat OPERATIONS \
| while read o macros prototypes
do
  [ -d "$o" ] || continue

  # for each operation, loop over primitives
  ls "$o" \
  | sort \
  | while read p
  do
    [ -d "$o/$p" ] || continue
    expectedchecksumbig=''
    [ -f "$o/$p/checksumbig" ] && expectedchecksumbig=`cat "$o/$p/checksumbig"`
    expectedchecksumsmall=''
    [ -f "$o/$p/checksumsmall" ] && expectedchecksumsmall=`cat "$o/$p/checksumsmall"`
    op="${o}_${p}"

    startdate=`date +%Y%m%d`

    # for each operation primitive, loop over abis
    okabi \
    | while read abi
    do
      echo "=== `date` === $abi $o/$p"
      libs=`"oklibs-$abi"`
      libs="$lib/$abi/cpucycles.o $libs"
      [ -f "$lib/$abi/libgmp.a" ] && libs="$lib/$abi/libgmp.a $libs"
      [ -f "$lib/$abi/libcryptopp.a" ] && libs="$lib/$abi/libcryptopp.a $libs"
      [ -f "$lib/$abi/lib${project}.a" ] && libs="$lib/$abi/lib${project}.a $libs"

      rm -rf "$work"
      mkdir -p "$work"
      mkdir -p "$work/best"
      mkdir -p "$work/bestc"

      # for each operation primitive abi, loop over implementations
      find "$o/$p" -follow -name "api.h" \
      | sort \
      | while read doth
      do
	implementationdir=`dirname $doth`
	opi=`echo "$implementationdir" | tr ./- ___`

        if [ -f "$implementationdir/architectures" ]
        then
          if grep '^'"$abi"'$' "$implementationdir/architectures" >/dev/null 
          then
            :
          else
            echo "=== `date` === skipping $abi/implementation/$implementationdir"
            continue
          fi
        fi

	echo "=== `date` === $abi $implementationdir"

	rm -rf "$work/compile"
	mkdir -p "$work/compile"
	cp -pr "$implementationdir"/* "$work/compile"
  
	cfiles=`ls "$work/compile" | grep '\.c$' || :`
	sfiles=`ls "$work/compile" | grep '\.[sS]$' || :`
	ccfiles=`ls "$work/compile" | grep '\.cc$' || :`
	cppfiles=`ls "$work/compile" | grep '\.cpp$' || :`

	language=c
	[ "x$cppfiles" = x ] || language=cpp
	[ "x$ccfiles" = x ] || language=cpp
  
	cp -p "$o/try.c" "$work/compile/try.$language"
	cp -p "$o/measure.c" "$work/compile/measure.$language"
	cp -p "try-anything.c" "$work/compile/try-anything.$language"
	cp -p "try.h" "$work/compile/try.h"
	cp -p "measure-anything.c" "$work/compile/measure-anything.$language"

	(
	  cd "$work/compile"
	  (
	    echo "#ifndef ${o}_H"
	    echo "#define ${o}_H"
	    echo ""
	    echo "#include \"${op}.h\""
	    echo ""
	    echo "$macros" | tr : '\012' | while read macro
	    do
	      echo "#define ${o}${macro} ${op}${macro}"
	    done
	    echo "#define ${o}_PRIMITIVE \"${p}\""
	    echo "#define ${o}_IMPLEMENTATION ${op}_IMPLEMENTATION"
	    echo "#define ${o}_VERSION ${op}_VERSION"
	    echo ""
	    echo "#endif"
	  ) > "$o.h"
	  (
	    echo "#ifndef ${op}_H"
	    echo "#define ${op}_H"
	    echo ""
	    sed 's/[ 	]CRYPTO_/ '"${opi}"'_/g' < api.h
	    echo ' '
	    echo '#ifdef __cplusplus'
	    echo 'extern "C" {'
	    echo '#endif'
	    echo "$prototypes" | tr : '\012' | while read prototype
	    do
	      echo "extern int ${opi}${prototype};"
	    done
	    echo '#ifdef __cplusplus'
	    echo '}'
	    echo '#endif'
	    echo ""
	    echo "$macros" | tr : '\012' | while read macro
	    do
	      echo "#define ${op}${macro} ${opi}${macro}"
	    done
	    echo "#define ${op}_IMPLEMENTATION \"${implementationdir}\""
	    echo "#ifndef ${opi}_VERSION"
	    echo "#define ${opi}_VERSION \"-\""
	    echo "#endif"
	    echo "#define ${op}_VERSION ${opi}_VERSION"
	    echo ""
	    echo "#endif"
	  ) > "$op.h"

	  ok${language}-$abi \
	  | while read compiler
	  do
	    echo "=== `date` === $abi $implementationdir $compiler"
	    compilerword=`echo "$compiler" | tr ' ' '_'`
	    ok=1
	    for f in $cfiles $sfiles $ccfiles $cppfiles
	    do
	      if [ "$ok" = 1 ]
	      then
		$compiler -DSUPERCOP \
		  -I. -I"$include" -I"$include/$abi" \
		  -c "$f" >../errors 2>&1 || ok=0
		( if [ `wc -l < ../errors` -lt 25 ]
		  then
		    cat ../errors
		  else
		    head ../errors
		    echo ...
		    tail ../errors
		  fi
		) \
		| while read err
		do
		  echo "$version $shorthostname $abi $startdate $o $p fromcompiler $implementationdir $compilerword $f $err" >&5
		done
	      fi
	    done

	    [ "$ok" = 1 ] || continue
	    okar-$abi cr "$op.a" *.o || continue
	    ranlib "$op.a"

	    killafter 300 \
	    $compiler -DSUPERCOP -DSMALL \
	      -I. -I"$include" -I"$include/$abi" \
	      -o try try.$language try-anything.$language \
	      "$op.a" $libs >../errors 2>&1 || ok=0
	    cat ../errors \
	    | while read err
	    do
	      echo "$version $shorthostname $abi $startdate $o $p fromcompiler $implementationdir $compilerword try.$language $err" >&5
	    done
	    [ "$ok" = 1 ] || continue

	    if sh -c 'killafter 3600 ./try || exit $?' >../outputs 2>../errors
	    then
	      checksumsmall=`awk '{print $1}' < ../outputs`
	      cycles=`awk '{print $2}' < ../outputs`
	      checksumcycles=`awk '{print $3}' < ../outputs`
	      cyclespersecond=`awk '{print $4}' < ../outputs`
	      impl=`awk '{print $5}' < ../outputs`
	    else
	      echo "$version $shorthostname $abi $startdate $o $p tryfails $implementationdir $compilerword error $?" >&5
	      cat ../outputs ../errors \
	      | while read err
	      do
	        echo "$version $shorthostname $abi $startdate $o $p tryfails $implementationdir $compilerword $err" >&5
	      done
	      continue
	    fi

	    [ x"$expectedchecksumsmall" != x ] \
	    && [ x"$expectedchecksumsmall" != "x$checksumsmall" ] \
	    && echo "$version $shorthostname $abi $startdate $o $p try $checksumsmall fails $cycles $checksumcycles $cyclespersecond $impl $compilerword" >&5 \
	    && continue

	    killafter 300 \
	    $compiler -DSUPERCOP \
	      -I. -I"$include" -I"$include/$abi" \
	      -o try try.$language try-anything.$language \
	      "$op.a" $libs >../errors 2>&1 || ok=0
	    cat ../errors \
	    | while read err
	    do
	      echo "$version $shorthostname $abi $startdate $o $p fromcompiler $implementationdir $compilerword try.$language $err" >&5
	    done
	    [ "$ok" = 1 ] || continue

	    if sh -c 'killafter 3600 ./try || exit $?' >../outputs 2>../errors
	    then
	      checksumbig=`awk '{print $1}' < ../outputs`
	      cycles=`awk '{print $2}' < ../outputs`
	      checksumcycles=`awk '{print $3}' < ../outputs`
	      cyclespersecond=`awk '{print $4}' < ../outputs`
	      impl=`awk '{print $5}' < ../outputs`
	    else
	      echo "$version $shorthostname $abi $startdate $o $p tryfails $implementationdir $compilerword error $?" >&5
	      cat ../outputs ../errors \
	      | while read err
	      do
	        echo "$version $shorthostname $abi $startdate $o $p tryfails $implementationdir $compilerword $err" >&5
	      done
	      continue
	    fi

	    [ x"$expectedchecksumbig" != x ] \
	    && [ x"$expectedchecksumbig" != "x$checksumbig" ] \
	    && echo "$version $shorthostname $abi $startdate $o $p try $checksumbig fails $cycles $checksumcycles $cyclespersecond $impl $compilerword" >&5 \
	    && continue

	    checksumok=ok
	    [ "x$expectedchecksumsmall" = "x" ] && checksumok=unknown
	    [ "x$expectedchecksumbig" = "x" ] && checksumok=unknown
	    echo "$version $shorthostname $abi $startdate $o $p try $checksumsmall/$checksumbig $checksumok $cycles $checksumcycles $cyclespersecond $impl $compilerword" >&5

	    [ -s ../bestc/median ] && [ `cat ../bestc/median` -le $cycles ] && continue

	    killafter 3600 \
	    $compiler -D'COMPILER="'"$compiler"'"' \
	      -DSUPERCOP -DLOOPS=3 \
	      -I. -I"$include" -I"$include/$abi" \
	      -o measure measure.$language measure-anything.$language \
	      "$op.a" $libs >../errors 2>&1 || ok=0
	    cat ../errors \
	    | while read err
	    do
	      echo "$version $shorthostname $abi $startdate $o $p fromcompiler $implementationdir $compilerword measure.$language $err" >&5
	    done
	    [ "$ok" = 1 ] || continue
  
	    for b in best bestc
	    do
	      [ $language = cpp ] && [ $b = bestc ] && continue
	      [ -s ../$b/median ] && [ `cat ../$b/median` -le $cycles ] && continue
	      echo "$cycles" > ../$b/median
	      rm -f ../$b/*.o ../$b/measure || continue
	      for f in *.o
	      do
	        cp -p "$f" "../$b/${opi}-$f"
	      done
	      cp -p "$op.h" "../$b/$op.h"
	      cp -p "$o.h" "../$b/$o.h"
	      cp -p measure ../$b/measure
	    done
	  done
	)
      done

      echo "=== `date` === $abi $o/$p measuring"

      "$work/best/measure" \
      | while read measurement
      do
	echo "$version $shorthostname $abi $startdate $o $p $measurement" >&5
      done

      [ -f "$o/$p/used" ] \
      && okar-$abi cr "$lib/$abi/lib${project}.a" "$work/bestc"/*.o \
      && ( ranlib "$lib/$abi/lib${project}.a" || exit 0 ) \
      && cp -p "$work/bestc/$op.h" "$include/$abi/$op.h" \
      && [ -f "$o/$p/selected" ] \
      && cp -p "$work/bestc/$o.h" "$include/$abi/$o.h" \
      || :
    done
  done
done

echo "=== `date` === finishing"

sed 's/^/+ /' <"$top/log" >&5
gzip -9 "$top/data"
touch "$top/done-$version"
