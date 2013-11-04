#                                               -*- Autoconf -*-
# Process this file with autoconf to produce a configure script.

AC_PREREQ([2.67])
AC_INIT([treetop], [0.1], [benjamin.villain@ucopia.fr])
AC_CONFIG_SRCDIR([main.c])
AC_CONFIG_HEADERS([config.h])
AM_INIT_AUTOMAKE

AC_DEFINE([PROG_NAME], ["treetop"], [Program name])

# Checks for programs.
AC_PROG_CC
AC_PROG_INSTALL
AC_PROG_RANLIB
AM_PROG_CC_C_O

# Checks for libraries.
# FIXME: Replace `main' with a function in `-lpthread':
AC_CHECK_LIB([pthread], [pthread_create])
# FIXME: Replace `main' with a function in `-lrt':
AC_CHECK_LIB([rt], [strtol])

# Checks for header files.
AC_CHECK_HEADERS([stdlib.h string.h sys/ioctl.h sys/stat.h unistd.h sys/event.h])

# Checks for typedefs, structures, and compiler characteristics.
AC_TYPE_SIZE_T

# Checks for library functions.
AC_FUNC_MALLOC
AC_CHECK_FUNCS([kqueue epoll_create])

AC_CONFIG_FILES([Makefile])
AC_OUTPUT
