#!/bin/sh

: ${BLST_VERSION:='v0.3.11'}
git clone --depth 1 --branch ${BLST_VERSION} https://github.com/supranational/blst
cd blst
./build.sh
cat > libblst.pc << EOF
prefix=/usr/local
exec_prefix=\${prefix}
libdir=\${exec_prefix}/lib
includedir=\${prefix}/include

Name: libblst
Description: Multilingual BLS12-381 signature library
URL: https://github.com/supranational/blst
Version: ${BLST_VERSION#v}
Cflags: -I\${includedir}
Libs: -L\${libdir} -lblst
EOF
cp libblst.pc /usr/local/lib/pkgconfig/
cp bindings/blst_aux.h bindings/blst.h bindings/blst.hpp  /usr/local/include/
cp libblst.a /usr/local/lib
