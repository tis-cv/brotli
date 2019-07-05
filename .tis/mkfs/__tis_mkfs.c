/**************************************************************************/
/*                                                                        */
/*  This file is part of TrustInSoft Mkfs Tool.                           */
/*                                                                        */
/*    Copyright (C) 2016-2018 TrustInSoft                                 */
/*                                                                        */
/*  TrustInSoft Mkfs Tool is released under GPLv2                         */
/*                                                                        */
/**************************************************************************/

#include "__fc_machdep.h"

#include <sys/socket.h>
#include <sys/mman.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdio.h>
#include <string.h>
#include <limits.h>

#include <tis_builtin.h>
//@ assigns *__fc_stdout \from format[..];
int tis_printf(const char *__restrict format, ...);
//@ assigns *stream \from format[..];
int tis_fprintf(FILE *__restrict stream, const char *__restrict format, ...);

#include <__tis_mkfs.h>

//==============================================================================
#ifdef __TIS_MKFS_NO_ERR
#define RETURN_RANDOM_ERROR(r)
#else
#define RETURN_RANDOM_ERROR(r) { \
  if (tis_nondet (0, 1)) { \
    tis_make_unknown((void*)(&errno), sizeof errno); \
    return (r); \
  } \
}
#endif // __TIS_MKFS_NO_ERR
//==============================================================================
#ifdef __TIS_MKFS_STATIC_ALLOCATE
#define __TIS_MKFS_STD_ALLOCATE
#elif defined __TIS_MKFS_PREALLOCATE
// the value of this variable must be provided externally
extern size_t __mkfs_preallocate_size;
static unsigned char * alloc_data (int ino, size_t st_size) {
  //@ assert file_fits_1: st_size <= __mkfs_preallocate_size ;
  return malloc (__mkfs_preallocate_size);
}
static unsigned char * realloc_data (unsigned char * old, size_t st_size) {
  //@ assert file_fits_2: st_size <= __mkfs_preallocate_size ;
  return old;
}
#elif defined __TIS_MKFS_DYNAMIC_ALLOCATE
static size_t __max(size_t a, size_t b) {
  return (a>b)?a:b;
}
static unsigned char * alloc_data (int ino, size_t st_size) {
  return malloc (__max (1, st_size));
}
static unsigned char * realloc_data (unsigned char * old, size_t st_size) {
  return realloc (old, __max (1, st_size));
}
#else
#define __TIS_MKFS_STD_ALLOCATE
#endif

#ifdef __TIS_MKFS_STD_ALLOCATE
// standard allocation mode: static array.
#define TIS_FSIZE INT_MAX
static const size_t mkfs_data_table_size = TIS_FSIZE;
static unsigned char mkfs_data_table[FOPEN_MAX][TIS_FSIZE];
static unsigned char * alloc_data (int ino, size_t st_size) {
  //@ assert file_fits_1: st_size <= mkfs_data_table_size ;
  return mkfs_data_table[ino];
}
static unsigned char * realloc_data (unsigned char * old, size_t st_size) {
  //@ assert file_fits_2: st_size <= mkfs_data_table_size ;
  return old;
}
#endif

//==============================================================================
// File descriptors
//------------------------------------------------------------------------------
// File descriptor management.
// The local information is only to store the kind of the opened object
// to be able to find its information in the appropriate array
//------------------------------------------------------------------------------
struct __mkfs_fd_info {
  int __mkfs_fd_kind; // S_IFREG (file)
                     // S_IFDIR (directory)
                     // S_IFCHR (stdin, stdout, stderr):
                     // S_IFIFO (pipe)
                     // S_IFSOCK (socket)
                     // 0 when the file descriptor is not used.
  int __mkfs_fd_index; // index for internal use.
};

// array of open file descriptors.
struct __mkfs_fd_info __mkfs_file_desc[FOPEN_MAX];

// set errno when \result == -1;
int __mkfs_check_fd_ok (int fd) {
  if (fd < 0 || fd >= FOPEN_MAX) {
    errno = EBADF;
    return -1;
  }
  return 0;
}

int __mkfs_get_fd_kind (int __fd) {
  return __mkfs_file_desc[__fd].__mkfs_fd_kind;
}

//------------------------------------------------------------------------------
// About files:
//------------------------------------------------------------------------------
static __mkfs_file_info mkfs_opened_files[FOPEN_MAX];

static int mkfs_get_next_file_index (void) {
  static size_t mkfs_next_file_index = 0;
  if (mkfs_next_file_index >= FOPEN_MAX)
    return -1;
  else
    return mkfs_next_file_index++;
}

__mkfs_file_info * __mkfs_get_file_info (int fd) {
  if (__mkfs_check_fd_ok (fd) != 0) return NULL;
  int kind = __mkfs_file_desc[fd].__mkfs_fd_kind;
  int idx = __mkfs_file_desc[fd].__mkfs_fd_index;
  if  (S_ISREG (kind) || S_ISCHR (kind) || S_ISFIFO (kind))
    return &mkfs_opened_files[idx];
  else
    return NULL;
}

//------------------------------------------------------------------------------
// About sockets:
//------------------------------------------------------------------------------
//
static __mkfs_socket_info mkfs_opened_socket[FOPEN_MAX];

__mkfs_socket_info * __mkfs_get_socket_info (int fd) {
  if (__mkfs_check_fd_ok (fd) != 0) return NULL;
  int kind = __mkfs_file_desc[fd].__mkfs_fd_kind;
  int idx = __mkfs_file_desc[fd].__mkfs_fd_index;
  if  (S_ISSOCK (kind))
    return &mkfs_opened_socket[idx];
  else
    return NULL;
}

//------------------------------------------------------------------------------
// About directories:
//------------------------------------------------------------------------------
//
// the directories info is in __fc_opendir (declared in dirent.h)

__mkfs_dir_info * __mkfs_get_dir_info (int fd) {
  if (__mkfs_check_fd_ok (fd) != 0) return NULL;
  int kind = __mkfs_file_desc[fd].__mkfs_fd_kind;
  int idx = __mkfs_file_desc[fd].__mkfs_fd_index;
  if  (S_ISDIR (kind))
    return &__fc_opendir[idx];
  else
    return NULL;
}

//==============================================================================

static struct stat * mk_inode (int mode) {
  // No need to dynamically allocate inodes.
  // There are already statically allocated for pre-existing objects.
  // This table is a pool of inodes to be used for new objects.
  static struct stat inode_table[FOPEN_MAX];
  static const size_t inode_nb_max = FOPEN_MAX;
  static int next_inode_index = 0;

  struct stat * st = next_inode_index < inode_nb_max ?
                     inode_table + next_inode_index++
                   : NULL;
  //@ assert no_more_inode_mkfs_niy: st != \null;
  st->st_ino = __mkfs_next_inode++;
  st->st_mode = mode;
  st->st_uid = __mkfs_uid;
  st->st_gid = __mkfs_gid;
  st->st_size = 0;
  st->st_nlink = 1;
  st->st_dev = __TIS_MKFS_ST_DEV;
  st->st_blksize = __TIS_MKFS_BLKSIZE;
  return st;
}

static __mkfs_file_info * init_fd_file (int fd, int kind, int flags,
    struct __mkfs_fs_file * file) {
  int file_idx = mkfs_get_next_file_index ();
  __mkfs_file_desc[fd].__mkfs_fd_index = file_idx,
  __mkfs_file_desc[fd].__mkfs_fd_kind = kind;

  __mkfs_file_info * f = &mkfs_opened_files[file_idx];

  f->__mkfs_position.__fc_stdio_position = 0;
  f->__mkfs_error = 0;
  f->__mkfs_eof = 0;
  f->__mkfs_flags = flags;
  f->__mkfs_file = file;

  return f;
}

struct __mkfs_fs_file __mkfs_fs_stdin, __mkfs_fs_stdout, __mkfs_fs_stderr;

/*@
// when this property is not valid, it is probably that the source file
// generated by tis-mkfs has not been provided to the analyzer.
requires mkfs_next_inode_definition:
0 <= __mkfs_next_inode && __mkfs_next_inode < INT_MAX; */
__attribute__((constructor))
  static void __mkfs_init_stdio (void) {
    mode_t r_mode = S_IFCHR | S_IRUSR | S_IRGRP | S_IROTH;
    __mkfs_fs_stdin.__mkfs_stat = mk_inode (r_mode);
    struct __mkfs_fs_file * stdin_file = __mkfs_get_file ("tis-mkfs-stdin");
    if (stdin_file) {
      char * content = stdin_file->__mkfs_content ();
      __mkfs_fs_stdin.__mkfs_data = content;
      __mkfs_fs_stdin.__mkfs_stat->st_size = stdin_file->__mkfs_stat->st_size;
    }
    init_fd_file (0, S_IFCHR, O_RDONLY, &__mkfs_fs_stdin);

    mode_t w_mode = S_IFCHR | S_IWUSR | S_IWGRP | S_IWOTH;

    __mkfs_fs_stdout.__mkfs_stat = mk_inode (w_mode);
    init_fd_file (1, S_IFCHR, O_WRONLY, &__mkfs_fs_stdout);

    __mkfs_fs_stderr.__mkfs_stat = mk_inode (w_mode);
    init_fd_file (2, S_IFCHR, O_WRONLY, &__mkfs_fs_stderr);
  }

// set errno when \result == -1;
static int get_next_file_desc (void) {
  int fd;
#ifndef __TIS_MKFS_NO_CLOSE
  /*@ slevel 1025; */
  for (fd = 0; fd < FOPEN_MAX; fd++) {
    if (__mkfs_file_desc[fd].__mkfs_fd_kind == 0) {
      break;
    }
  }
  /*@ slevel default; */
#else // __TIS_MKFS_NO_CLOSE
  static int __mkfs_next_fd = 3;
  fd = __mkfs_next_fd++;
#endif // __TIS_MKFS_NO_CLOSE
  if (fd < FOPEN_MAX) {
    return fd;
  }

  RETURN_RANDOM_ERROR (-1);

  errno = EMFILE;
  return -1;
}

// set errno when \result == -1;
int __mkfs_check_fd_file_ok (int fd) {
  if  (S_ISDIR (__mkfs_file_desc[fd].__mkfs_fd_kind)) {
    errno = EISDIR;
    return -1;
  }
  __mkfs_file_info * file_info = __mkfs_get_file_info (fd);
  if (file_info == NULL || file_info->__mkfs_file == NULL) {
    errno = EBADF;
    return -1;
  }
  RETURN_RANDOM_ERROR (-1);
  return 0;
}
// set errno when \result == -1;
int __mkfs_check_fd_dir_ok (int fd) {
  __mkfs_dir_info * dir = __mkfs_get_dir_info (fd);
  if (dir == NULL) {
    errno = EBADF;
    return -1;
  }
  if ( dir->__fc_dir_id != fd || dir->__fc_dir_inode == NULL) {
    errno = EBADF;
    return -1;
  }
  RETURN_RANDOM_ERROR (-1);
  return 0;
}
// set errno when \result == -1;
int __mkfs_check_fd_socket_ok (int fd) {
  __mkfs_socket_info * socket = __mkfs_get_socket_info (fd);
  if (socket == NULL) {
    errno = EBADF;
    return -1;
  }
  RETURN_RANDOM_ERROR (-1);
  return 0;
}

//==============================================================================
// About files : stdio.h, unistd.h and sys/stat.h functions.
//==============================================================================
// Getting information: 'stat' and 'getxxx' functions
//------------------------------------------------------------------------------
// set errno when \result == -1;
/*@ requires tis_access_mode:
  (mode & (__mkfs_R_OK | __mkfs_W_OK | __mkfs_X_OK)) == mode;
  */
static int stat_access (struct stat * st, int mode) {
  mode_t m = st->st_mode;
  int ok;
  if (st->st_uid == __mkfs_euid) {
    ok = 1;
    ok = (mode & R_OK) ? ok && (m & S_IRUSR) : ok;
    ok = (mode & W_OK) ? ok && (m & S_IWUSR) : ok;
    ok = (mode & X_OK) ? ok && (m & S_IXUSR) : ok;
  }
  else if (st->st_uid == __mkfs_egid) {
    ok = 1;
    ok = (mode & R_OK) ? ok && (m & S_IRGRP) : ok;
    ok = (mode & W_OK) ? ok && (m & S_IWGRP) : ok;
    ok = (mode & X_OK) ? ok && (m & S_IXGRP) : ok;
  }
  else {
    ok = 1;
    ok = (mode & R_OK) ? ok && (m & S_IROTH) : ok;
    ok = (mode & W_OK) ? ok && (m & S_IWOTH) : ok;
    ok = (mode & X_OK) ? ok && (m & S_IXOTH) : ok;
  }
  if (ok) {
    RETURN_RANDOM_ERROR (-1);
    return 0;
  }
  else {
    errno = EBADF;
    return -1;
  }
}
// set errno when \result == -1;
int __mkfs_check_fd_file_ok_for_reading (int fd) {
  int ret = __mkfs_check_fd_file_ok (fd); // handle __TIS_MKFS_NO_ERR
  if (ret == -1)
    // errno already set in __mkfs_check_fd_file_ok
    return -1;
  __mkfs_file_info * file_info = __mkfs_get_file_info (fd);
  if (file_info->__mkfs_flags & O_WRONLY) {
    errno = EBADF;
    return -1;
  }
  ret = stat_access (file_info->__mkfs_file->__mkfs_stat, R_OK);
  return ret;
}

// set errno when \result == -1;
int __mkfs_check_fd_file_ok_for_writing (int fd) {
  int ret = __mkfs_check_fd_file_ok (fd); // handle __TIS_MKFS_NO_ERR
  if (ret == -1)
    // errno already set in __mkfs_check_fd_file_ok
    return -1;
  __mkfs_file_info * file_info = __mkfs_get_file_info (fd);
  if (!(file_info->__mkfs_flags & O_WRONLY) &&
      !(file_info->__mkfs_flags & O_RDWR)) {
    errno = EBADF;
    return -1;
  }
  ret = stat_access (file_info->__mkfs_file->__mkfs_stat, W_OK);
  return ret;
}

// set errno when \result == -1;
int __mkfs_fstat(int fd, struct stat *buf) {
  int ret = __mkfs_check_fd_ok (fd); // handle __TIS_MKFS_NO_ERR
  if (ret == -1)
    // errno already set in __mkfs_check_fd_file_ok
    return -1;
  struct stat * st;
  if (S_ISREG (__mkfs_file_desc[fd].__mkfs_fd_kind)
      ||  S_ISFIFO (__mkfs_file_desc[fd].__mkfs_fd_kind)) {
    __mkfs_file_info * file_info = __mkfs_get_file_info (fd);
    st = file_info->__mkfs_file->__mkfs_stat;
  }
  else if  (S_ISDIR (__mkfs_file_desc[fd].__mkfs_fd_kind)) {
    __mkfs_dir_info * dir_info = __mkfs_get_dir_info (fd);
    st = dir_info->__fc_dir_inode;
  }
  else {
    errno = EBADF;
    return -1;
  }
  *buf = *st;
  return 0;
}
#ifndef __TIS_USER_FSTAT
int fstat(int __fd, struct stat *__buf) {
  return __mkfs_fstat(__fd, __buf);
}
#endif // __TIS_USER_FSTAT

// set errno when \result == -1;
int __mkfs_stat(const char *pathname, struct stat *buf) {
  struct __mkfs_fs_file * fs = __mkfs_get_file (pathname);
  if (fs != NULL) {
    RETURN_RANDOM_ERROR (-1);
    *buf = *(fs->__mkfs_stat);
    return 0;
  }
  struct __mkfs_fs_dir * d = __mkfs_get_dir (pathname);
  if (d != NULL) {
    RETURN_RANDOM_ERROR (-1);
    *(buf) = *(d->__mkfs_stat);
    return 0;
  }
  RETURN_RANDOM_ERROR (-1);
  errno = ENOENT;
  return -1;
}
#ifndef __TIS_USER_STAT
int stat(const char *__restrict __path, struct stat *__restrict __buf) {
  return __mkfs_stat(__path, __buf);
}
#endif //__TIS_USER_STAT

int __mkfs_lstat(const char *pathname, struct stat *buf) {
  int ret = stat (pathname, buf);
  if (0 == ret) {
    if (S_ISLNK (buf->st_mode)) {
      //@ assert lstat_links_mkfs_niy: WARN_NIY ;
      return -1;
    }
    return ret;
  }
  return ret;
}
#ifndef __TIS_USER_LSTAT
int lstat(const char *__restrict __path, struct stat *__restrict __buf) {
  return __mkfs_lstat(__path, __buf);
}
#endif // __TIS_USER_LSTAT

// set errno when \result == -1;
int __mkfs_access(const char *pathname, int mode) {
  struct stat buf_stat;
  if (mode != F_OK && (mode & (R_OK | W_OK | X_OK) != mode)) {
    errno = EINVAL;
    return -1;
  }
  if (0 == stat (pathname, &buf_stat)) { // know element: test mode
    if (mode == F_OK) return 0;
    return stat_access (&buf_stat, mode); // handle __TIS_MKFS_NO_ERR
  }
  else { // unknown file or directory
    tis_make_unknown ((void*)&errno, sizeof (errno));
    return -1;
  }
}
#ifndef __TIS_USER_ACCESS
int access(const char *pathname, int mode)
{ return __mkfs_access(pathname, mode); }
#endif // __TIS_USER_ACCESS

uid_t __mkfs_getuid(void) { return __mkfs_uid; }
#ifndef __TIS_USER_GETUID
uid_t getuid(void) { return __mkfs_getuid(); }
#endif // __TIS_USER_GETUID

uid_t __mkfs_geteuid(void) { return __mkfs_euid; }
#ifndef __TIS_USER_GETEUID
uid_t geteuid(void) { return __mkfs_geteuid(); }
#endif // __TIS_USER_GETEUID

uid_t __mkfs_getgid(void) { return __mkfs_gid; }
#ifndef __TIS_USER_GETGID
uid_t getgid(void) { return __mkfs_getgid(); }
#endif // __TIS_USER_GETGID

uid_t __mkfs_getegid(void) { return __mkfs_egid; }
#ifndef __TIS_USER_GETEGID
uid_t getegid(void) { return __mkfs_getegid(); }
#endif // __TIS_USER_GETEGID

//==============================================================================
// 'open' file functions
//------------------------------------------------------------------------------
// everything is checked already : just do it.
// set errno when \result == -1;
//@ requires file_fd: kind == S_IFREG || kind == S_IFIFO || kind == S_IFCHR;
static int open_fd (int fd, int kind, int flags, unsigned char * content,
    struct __mkfs_fs_file * file) {

   struct stat * st = file->__mkfs_stat;

  __mkfs_file_info * file_info = init_fd_file (fd, kind, flags, file);

  if ((flags & O_TRUNC) && ((flags & O_WRONLY) || (flags & O_RDWR))) {
    st->st_size = 0;
  }

  if (file->__mkfs_data == NULL && (content || flags & O_CREAT)) {
    unsigned char * ptr = alloc_data (st->st_ino, st->st_size);
    if (ptr == NULL) {
      errno = ENOMEM;
      return -1;
    }
    if (st->st_size > 0)
      memcpy (ptr, content, st->st_size);
    file->__mkfs_data = ptr;
  }

  return 0;
}

// set errno when \result == -1;
static struct __mkfs_fs_file * create_file (const char * filename, int mode) {
  if (__mkfs_fs_files_nb >= __mkfs_fs_files_nb_max) {
    // use -nb-max-created-files to increase the maximum.
    errno = EMFILE;
    return NULL;
  }

  //@ assert register_new_file_in_dirent_niy: WARN_NIY ;

  RETURN_RANDOM_ERROR (NULL);

  char * filename2 = strdup (filename);
#ifndef __TIS_MKFS_NO_ERR
  if (filename2 == NULL) {
    errno = ENOMEM;
    return NULL;
  }
#else
  //@ assert tis_mkfs_fopen_strdup_ok: filename2 != \null;
#endif

  struct stat * st = mk_inode (S_IFREG | mode);
  int f = __mkfs_fs_files_nb++;
  struct __mkfs_fs_file * file = __mkfs_fs_files + f;
  file->__mkfs_fullpath = filename2;
  file->__mkfs_stat = st;
  file->__mkfs_content = NULL;
  return file;
}

// set errno when \result == -1;
/*@ requires tis_open_flags: ((flags & __mkfs_O_RDONLY) == __mkfs_O_RDONLY)
  || ((flags & __mkfs_O_WRONLY) == __mkfs_O_WRONLY)
  || ((flags & __mkfs_O_RDWR) == __mkfs_O_RDWR);
  */
static int open_file (const char * filename, int flags, int mode) {
  struct __mkfs_fs_file * file = __mkfs_get_file (filename);
  if (flags & O_CREAT) {
    if (file == NULL) {
      file = create_file (filename, mode); // handle __TIS_MKFS_NO_ERR
      if (file == NULL)
        return -1; // errno already set create_file
    }
    else if (flags & O_EXCL) {
      errno = EEXIST;
      return -1;
    }
  }
  if (file != NULL) {
    struct stat * st = file->__mkfs_stat;
    if ((flags & O_RDONLY) || (flags & O_RDWR)) {
      if (-1 == stat_access (st, R_OK)) // handle __TIS_MKFS_NO_ERR
        // errno already set in stat_access
        return -1;
    }
    if ((flags & O_WRONLY) || (flags & O_RDWR)) {
      if (-1 == stat_access (st, W_OK)) // handle __TIS_MKFS_NO_ERR
        // errno already set in stat_access
        return -1;
    }
    int fd = get_next_file_desc (); // handle __TIS_MKFS_NO_ERR
    if (fd != -1) {
      char * content = file->__mkfs_content ? (file->__mkfs_content ()) : NULL;
      int kind = S_ISREG (st->st_mode) ? S_IFREG
               : S_ISFIFO (st->st_mode) ? S_IFIFO
               : S_ISCHR (st->st_mode) ? S_IFCHR
               : -1; // invalid value will break in open_fd
      int res = open_fd (fd, kind, flags, content, file);
      if (res != 0)
        return res;
    }
    // else errno already set in get_next_file_desc
    return fd;
  }
  errno = ENOENT;
  return -1;
}
int __mkfs_open(const char * filename, int flags, va_list va) {
  int mode;
  if (flags & __mkfs_O_CREAT) {
    mode = va_arg(va, int);
  } else {
    mode = S_IRUSR | S_IWUSR | S_IRGRP | S_IWGRP | S_IROTH | S_IWOTH;
  }
  return open_file (filename, flags, mode); // handle __TIS_MKFS_NO_ERR
}
#ifndef __TIS_USER_OPEN
int open(const char * filename, int flags, ...) {
  va_list va;
  va_start(va, flags);
  int rv = __mkfs_open(filename, flags, va);
  va_end(va);
  return rv;
}
#endif // __TIS_USER_OPEN

int __mkfs_creat(const char *filename, mode_t mode) {
  int flags = O_WRONLY|O_CREAT|O_TRUNC;
  return open_file (filename, flags, mode); // handle __TIS_MKFS_NO_ERR
}
#ifndef __TIS_USER_CREAT
int creat(const char *filename, mode_t mode) {
  return __mkfs_creat (filename, mode);
}
#endif // __TIS_USER_CREAT

// set errno when \result == -1;
int __mkfs_dup2(int oldfd, int newfd) {
  if (__mkfs_check_fd_ok(oldfd) == -1)
    return -1;
  if (__mkfs_file_desc[oldfd].__mkfs_fd_kind == 0) {
    errno = EBADF;
    return -1;
  }
  if (__mkfs_check_fd_ok(newfd) == -1)
    return -1;
  if (newfd == oldfd)
    return newfd;
  if (__mkfs_file_desc[newfd].__mkfs_fd_kind != 0)
    close(newfd);
  __mkfs_file_desc[newfd].__mkfs_fd_kind =
    __mkfs_file_desc[oldfd].__mkfs_fd_kind;
  __mkfs_file_desc[newfd].__mkfs_fd_index =
    __mkfs_file_desc[oldfd].__mkfs_fd_index;

  return newfd;
}
#ifndef __TIS_USER_DUP2
/* @ TODO ?
  assigns __FC_errno, \result \from __fd, __fd2, __fc_fds[..];
  assigns __mkfs_file_desc[__fd2] \from __fd, __fd2, __mkfs_file_desc[__fd];
*/
int dup2(int __fd, int __fd2)
{ return __mkfs_dup2(__fd, __fd2); }
#endif // __TIS_USER_DUP2

int __mkfs_dup(int oldfd) {
  return dup2(oldfd, get_next_file_desc());
}
#ifndef __TIS_USER_DUP
/* @ TODO ?
  assigns __mkfs_file_desc[..] \from oldfd, __mkfs_file_desc[..]; */
int dup(int oldfd)
{ return __mkfs_dup(oldfd); }
#endif // __TIS_USER_DUP

//==============================================================================
// 'fcntl' (only a few commands are implemented at the moment)
//------------------------------------------------------------------------------

int __mkfs_fcntl(int __fd, int __cmd, va_list ap) {
  int ret = __mkfs_check_fd_file_ok (__fd); // handle __TIS_MKFS_NO_ERR
  if (ret != 0) {
    // errno already set
    return ret;
  }
  switch (__cmd) {
    case F_GETFL: {
      __mkfs_file_info * file_info = __mkfs_get_file_info (__fd);
      ret = file_info->__mkfs_flags;
      break;
      }
    default:
      //@ assert fcntl_cmd_niy: WARN_NIY ;
      if (tis_nondet (0, 1)) {
        tis_make_unknown((void*)&errno, sizeof errno);
        return -1;
      }
      else {
        tis_make_unknown((void*)&ret, sizeof ret);
      }
  }
  return ret;
}
#ifndef __TIS_USER_FCNTL
int fcntl(int __fd, int __cmd, ...) {
  va_list va;
  va_start(va, __cmd);
  int rv = __mkfs_fcntl(__fd, __cmd, va);
  va_end(va);
  return rv;
}
#endif
//==============================================================================
// 'read' file functions
//------------------------------------------------------------------------------
static ssize_t local_pread (int fd, void *buf, size_t count, off_t offset) {
  if (offset < 0) {
    errno = EINVAL;
    return -1;
  }
  int ret = __mkfs_check_fd_file_ok_for_reading (fd); // handle __TIS_MKFS_NO_ERR
  if (ret != 0) {
    return ret;
  }
  __mkfs_file_info * file_info = __mkfs_get_file_info (fd);
  struct stat * st = file_info->__mkfs_file->__mkfs_stat;
  size_t max = st->st_size;
  if (offset >= max)
    return 0;
  size_t n_avail = max - offset;
  size_t n_read = (n_avail >= count) ? count : n_avail;
  unsigned char * data = file_info->__mkfs_file->__mkfs_data;
  if (data)
    memcpy (buf, data + offset, n_read);
  else
    tis_make_unknown ((char*)buf, n_read);
  return n_read;
}

static ssize_t read_file(int fd, void *buf, size_t count) {
  __mkfs_file_info * file_info = __mkfs_get_file_info (fd);
  unsigned long pos = file_info->__mkfs_position.__fc_stdio_position;
  ssize_t n_read = local_pread (fd, buf, count, pos); // handle __TIS_MKFS_NO_ERR
  if (n_read > 0) {
    file_info->__mkfs_position.__fc_stdio_position += n_read;
  }
  return n_read;
}
static ssize_t read_socket(int fd, void *buf, size_t count) {
  ssize_t res = tis_long_long_interval(-1, count);
  if (res == -1) {
#ifdef __TIS_MKFS_NO_ERR
    res = 0;
#else
    tis_make_unknown((void*)&errno, sizeof(errno));
#endif
    return res;
  }
  tis_make_unknown(buf, res);
  return res;
}
ssize_t __mkfs_read(int fd, void *buf, size_t count) {
  if (fd < 0 || fd >= FOPEN_MAX) {
    errno = EBADF;
    return -1;
  }
  switch (__mkfs_file_desc[fd].__mkfs_fd_kind) {
    case 0: errno = EBADF; return -1;
    case S_IFIFO:
    case S_IFCHR:
    case S_IFREG: return read_file(fd, buf, count);
    case S_IFDIR: errno = EISDIR; return -1;
    case S_IFSOCK: return read_socket(fd, buf, count);
    default: tis_make_unknown ((void*)&errno, sizeof (errno));
             return -1;
  }
}
#ifndef __TIS_USER_READ
/* @ TODO ?
   assigns mkfs_opened_files[..]._fc_position.__fc_stdio_position
  \from mkfs_opened_files[..]._fc_position.__fc_stdio_position,
  fd, __mkfs_file_desc[fd], count;
*/
ssize_t read(int fd, void *buf, size_t count)
{ return __mkfs_read(fd, buf, count); }
#endif // __TIS_USER_READ

ssize_t __mkfs_pread(int fd, void *buf, size_t count, off_t offset) {
  return local_pread (fd, buf, count, offset); // handle __TIS_MKFS_NO_ERR
}
#ifndef __TIS_USER_PREAD
/* @ TODO ?
  assigns mkfs_opened_files[..]._fc_position.__fc_stdio_position
  \from mkfs_opened_files[..]._fc_position.__fc_stdio_position,
  fd, __mkfs_file_desc[fd], count, offset;
*/
ssize_t pread(int fd, void *buf, size_t count, off_t offset)
{ return __mkfs_pread(fd, buf, count, offset); }
#endif // __TIS_USER_PREAD

int __mkfs_ungetc(int c, int fd) {
  int ret = __mkfs_check_fd_file_ok_for_reading (fd); // handle __TIS_MKFS_NO_ERR
  if (ret != 0)
    return EOF;
  __mkfs_file_info * file_info = __mkfs_get_file_info (fd);
  unsigned char *data = file_info->__mkfs_file->__mkfs_data;
  if (data) {
    int pos = file_info->__mkfs_position.__fc_stdio_position - 1;
    data[pos] = (unsigned char)c;
    file_info->__mkfs_position.__fc_stdio_position = pos;
  }
  file_info->__mkfs_eof = 0;
  RETURN_RANDOM_ERROR (EOF);
  return c;
}

//==============================================================================
// 'write' file functions
//------------------------------------------------------------------------------

/* to be used each time __mkfs_data[..] needs to be modified:
   in __mkfs_pwrite, __mkfs_fputc, __mkfs_fputs, ...
   Only handle __mkfs_data content. Depending on the case,
   the caller may also have to update the position and st_size.
   */
static int write__mkfs_data (__mkfs_file_info *file_info, off_t offset,
    const void *buf, size_t count) {
  if (file_info->__mkfs_file->__mkfs_data) {
    if (offset + count > file_info->__mkfs_file->__mkfs_stat->st_size) {
      unsigned char * ptr;
      ptr = realloc_data (file_info->__mkfs_file->__mkfs_data, offset + count);
#ifndef __TIS_MKFS_NO_ERR
      if (ptr == NULL) {
        tis_make_unknown ((void*)&errno, sizeof (errno));
        return -1;
      }
#else
      //@ assert write_no_err_realloc_ok: ptr != \null;
#endif // __TIS_MKFS_NO_ERR
      file_info->__mkfs_file->__mkfs_data = ptr;
    }
    memcpy (file_info->__mkfs_file->__mkfs_data + offset, buf, count);
  }
  else if (file_info->__mkfs_file == &__mkfs_fs_stdout) {
    if (count <= (size_t)INT_MAX)
      tis_printf ("%.*s", (int)count, (const char *)buf);
  }
  else if (file_info->__mkfs_file == &__mkfs_fs_stderr) {
    if (count <= (size_t)INT_MAX)
      tis_fprintf (stderr, "%.*s", (int)count, (const char *)buf);
  }
  return count;
}


// set errno when \result == -1;
static ssize_t local_pwrite (int fd, const void *buf,
                             size_t count, off_t offset) {
  if (offset < 0) {
    errno = EINVAL;
    return -1;
  }
  int ret = __mkfs_check_fd_file_ok_for_writing (fd); // handle __TIS_MKFS_NO_ERR
  if (ret == -1)
    return -1;
  __mkfs_file_info * file_info = __mkfs_get_file_info (fd);
  if (count == 0)
    return 0;
  if (file_info->__mkfs_flags & O_APPEND)
    offset = file_info->__mkfs_file->__mkfs_stat->st_size;

  ret = write__mkfs_data (file_info, offset, buf, count);
  if (ret == -1)
    return -1;
  //@ assert mkfs_pwrite_ok: ret == count;
  if (file_info->__mkfs_file->__mkfs_data) {
    // if this write leaves a hole, fill it with zeros
    if (offset > file_info->__mkfs_file->__mkfs_stat->st_size)
      memset (file_info->__mkfs_file->__mkfs_data + file_info->__mkfs_file->__mkfs_stat->st_size,
          0, offset - file_info->__mkfs_file->__mkfs_stat->st_size);
  }
  if (offset + count > file_info->__mkfs_file->__mkfs_stat->st_size)
    file_info->__mkfs_file->__mkfs_stat->st_size = offset + count;
  return count;
}
static ssize_t write_file(int fd, const void *buf, size_t count) {
  __mkfs_file_info * file_info = __mkfs_get_file_info (fd);
  unsigned long pos = file_info->__mkfs_position.__fc_stdio_position;
  ssize_t n_write =
    local_pwrite (fd, buf, count, pos); // handle __TIS_MKFS_NO_ERR
                                        // update st_size
  if (n_write > 0) {
    if (file_info->__mkfs_flags & O_APPEND)
      file_info->__mkfs_position.__fc_stdio_position =
        file_info->__mkfs_file->__mkfs_stat->st_size;
    else
      file_info->__mkfs_position.__fc_stdio_position += n_write;
  }
  return n_write;
}
static ssize_t write_socket(int fd, const void *buf, size_t count) {
  ssize_t res = tis_long_long_interval(-1, count);
#ifdef __TIS_MKFS_NO_ERR
  if (res == -1) res = 0;
#else
  if (res == -1) tis_make_unknown((void*)&errno, sizeof errno);
#endif
  return res;
}
// set errno when \result == -1;
ssize_t __mkfs_write(int fd, const void *buf, size_t count) {
  int ret = __mkfs_check_fd_file_ok_for_writing (fd); // handle __TIS_MKFS_NO_ERR
  if (ret == -1)
    return -1;
  switch (__mkfs_file_desc[fd].__mkfs_fd_kind) {
    case 0: errno = EBADF; return -1;
    case S_IFIFO:
    case S_IFCHR:
    case S_IFREG: return write_file(fd, buf, count);
    case S_IFDIR: errno = EISDIR; return -1;
    case S_IFSOCK: return write_socket(fd, buf, count);
    default: tis_make_unknown((void*)&errno, sizeof errno);
             return -1;
  }
}
#ifndef __TIS_USER_WRITE
/* @ TODO ?
   assigns mkfs_opened_files[..]._fc_position.__fc_stdio_position
      \from mkfs_opened_files[..]._fc_position.__fc_stdio_position,
            fd, __mkfs_file_desc[fd], count;
  assigns mkfs_opened_files[..].__mkfs_file->__mkfs_data[..]
    \from mkfs_opened_files[..].__mkfs_file->__mkfs_data[..],
          fd, __mkfs_file_desc[fd], count;
*/
ssize_t write(int fd, const void *buf, size_t count)
{ return __mkfs_write(fd, buf, count); }
#endif // __TIS_USER_WRITE

ssize_t __mkfs_pwrite(int fd, const void *buf, size_t count, off_t offset) {
  // __mkfs_position is not changed on purpose (see man)
  return local_pwrite (fd, buf, count, offset); // handle __TIS_MKFS_NO_ERR
}
#ifndef __TIS_USER_PWRITE
/* @ TODO ?
 assigns mkfs_opened_files[..]._fc_position.__fc_stdio_position
      \from mkfs_opened_files[..]._fc_position.__fc_stdio_position,
            fd, __mkfs_file_desc[fd], count, offset;
  assigns mkfs_opened_files[..].__mkfs_file->__mkfs_data[..]
    \from mkfs_opened_files[..].__mkfs_file->__mkfs_data[..],
          fd, __mkfs_file_desc[fd], count, offset;
*/
ssize_t pwrite(int fd, const void *buf, size_t count, off_t offset)
{ return __mkfs_pwrite(fd, buf, count, offset); }
#endif // __TIS_USER_PWRITE

//==============================================================================
// Offset functions (about fd position)
//------------------------------------------------------------------------------

int __mkfs_seekable (int fd) {
  if (fd < 0 || fd >= FOPEN_MAX
      || __mkfs_file_desc[fd].__mkfs_fd_kind != S_IFREG) {
    errno = EBADF;
    return -1;
  }
  RETURN_RANDOM_ERROR (-1);
  return 0;
}

off_t __mkfs_lseek(int fd, off_t offset, int whence) {
  if (__mkfs_seekable (fd) == -1) // handle __TIS_MKFS_NO_ERR
    return (off_t)(-1);

  __mkfs_file_info * file_info = __mkfs_get_file_info (fd);
  off_t new_off;
  switch (whence) {
    case SEEK_SET:
      new_off = offset;
      break;
    case SEEK_END:
      new_off = file_info->__mkfs_file->__mkfs_stat->st_size + offset;
      break;
    case SEEK_CUR:
      new_off = file_info->__mkfs_position.__fc_stdio_position + offset;
      break;
    default:
      errno = EINVAL;
      return (off_t)(-1);
  }
  if (new_off < 0) {
    errno = EINVAL;
    return (off_t)(-1);
  }
  file_info->__mkfs_position.__fc_stdio_position = new_off;
  return new_off;
}
#ifndef __TIS_USER_LSEEK
/* @ TODO ?
  assigns mkfs_opened_files[..]._fc_position.__fc_stdio_position
             \from mkfs_opened_files[..]._fc_position.__fc_stdio_position,
             fd, offset, whence, __mkfs_file_desc[fd];
*/
off_t lseek(int fd, off_t offset, int whence)
{ return __mkfs_lseek(fd, offset, whence); }
#endif // __TIS_USER_LSEEK

//==============================================================================
// 'truncate' functions
//------------------------------------------------------------------------------

// set errno when \result == -1;

// set errno when \result == -1;
int __mkfs_ftruncate(int fd, off_t length) {
  int ret = __mkfs_check_fd_file_ok_for_writing (fd); // handle __TIS_MKFS_NO_ERR
  if (ret == -1)
    return -1;
  __mkfs_file_info * file_info = __mkfs_get_file_info (fd);
  struct stat * st = file_info->__mkfs_file->__mkfs_stat;
  ret = stat_access (st, W_OK); // handle __TIS_MKFS_NO_ERR
  if (ret != 0)
    return ret;
  if (length < 0) {
    errno = EINVAL;
    return -1;
  }
  if (file_info->__mkfs_file->__mkfs_data) {
    unsigned char * ptr;
    ptr = realloc_data (file_info->__mkfs_file->__mkfs_data, length);
#ifndef __TIS_MKFS_NO_ERR
    if (ptr == NULL) {
      tis_make_unknown((void*)&errno, sizeof errno);
      return -1;
    }
#else
    //@ assert truncate_no_err_realloc_ok: ptr != \null;
#endif // __TIS_MKFS_NO_ERR
    if (length > st->st_size)
      memset (ptr + st->st_size, 0, length - st->st_size);
    file_info->__mkfs_file->__mkfs_data = ptr;
  }
  st->st_size = length;
  return 0;
}
#ifndef __TIS_USER_FTRUNCATE
/* @ TODO ?
    assigns file_info->__mkfs_file->__mkfs_data
      \from file_info->__mkfs_file->__mkfs_data, length;
    assigns file_info->__mkfs_file->__mkfs_data[..]
      \from file_info->__mkfs_file->__mkfs_data[..], length;
*/
int ftruncate(int fd, off_t length)
{ return __mkfs_ftruncate(fd, length); }
#endif // __TIS_USER_FTRUNCATE

// set errno when \result == -1;
int __mkfs_truncate(const char *filename, off_t length) {
  struct __mkfs_fs_file * file = __mkfs_get_file (filename);
  if (file != NULL) {
    struct stat * st = file->__mkfs_stat;
    int ret = stat_access (st, W_OK); // handle __TIS_MKFS_NO_ERR
    if (ret != 0)
      return ret;

    st->st_size = length;
    file->__mkfs_content = NULL;
    return 0;
  }
  errno = ENOENT;
  return -1;
}
#ifndef __TIS_USER_TRUNCATE
int truncate(const char *filename, off_t length)
{ return __mkfs_truncate(filename, length); }
#endif // __TIS_USER_TRUNCATE

// set errno when \result == -1;
static int close_file(int fd) {
  __mkfs_file_info * file_info = __mkfs_get_file_info (fd);
  int res = __mkfs_check_fd_file_ok (fd); // handle __TIS_MKFS_NO_ERR
  if (res == -1)
    return -1;
  __mkfs_file_desc[fd].__mkfs_fd_kind = 0;
  // make sure it won't be used anymore (see dup)
  file_info->__mkfs_file = NULL;
  return 0;
}

//==============================================================================
// About directories : dirent.h functions.
//==============================================================================

// set errno when \result == -1;
static int opendir_fd (const char * pathname) {
  struct __mkfs_fs_dir * dir = __mkfs_get_dir (pathname);
  if (dir != NULL) {
    struct stat * st = dir->__mkfs_stat;
    if (-1 == stat_access (st, R_OK)) // handle __TIS_MKFS_NO_ERR
      // errno already set in stat_access (EACCES)
      return -1;
    int fd = get_next_file_desc (); // handle __TIS_MKFS_NO_ERR
    if (fd != -1) {
      __mkfs_file_desc[fd].__mkfs_fd_kind = S_IFDIR;
      __mkfs_file_desc[fd].__mkfs_fd_index = fd;
      __mkfs_dir_info * dir_info = __mkfs_get_dir_info (fd);
      dir_info->__fc_dir_id = fd;
      dir_info->__fc_dir_position = 0;
      dir_info->__fc_dir_inode = st;
      dir_info->__fc_dir_entries = dir->__mkfs_dir_entries;
    }
    // else errno already set in get_next_file_desc (ENFILE)
    return fd;
  }
  tis_make_unknown((void*)&errno, sizeof errno);
  return -1;
}

// set errno when \result == NULL;
DIR * __mkfs_fdopendir (int fd) {
  __mkfs_dir_info * d = __mkfs_get_dir_info (fd);
  if (d == NULL) {
    errno = EBADF;
    return NULL;
  }
  RETURN_RANDOM_ERROR (NULL);
  return d;
}
#ifndef __TIS_USER_FDOPENDIR
DIR * fdopendir (int fd)
{ return __mkfs_fdopendir(fd); }
#endif // __TIS_USER_FDOPENDIR

// set errno when \result == NULL;
DIR *__mkfs_opendir(const char * restrict path) {
  int fd = opendir_fd (path); // handle __TIS_MKFS_NO_ERR
  if (fd != -1) {
    __mkfs_dir_info * d = __mkfs_get_dir_info (fd);
    return d;
  }
  return NULL;

}
#ifndef __TIS_USER_OPENDIR
DIR *opendir(const char * restrict path)
{ return __mkfs_opendir(path); }
#endif // __TIS_USER_OPENDIR

int __mkfs_dirfd(DIR *dirp) {
  int fd = dirp->__fc_dir_id;
  int res = __mkfs_check_fd_dir_ok (fd); // handle __TIS_MKFS_NO_ERR
  if (res != 0)
    return res;
  return fd;
}
#ifndef __TIS_USER_DIRFD
int dirfd(DIR *dirp)
{ return __mkfs_dirfd(dirp); }
#endif // __TIS_USER_DIRFD

long __mkfs_telldir(DIR *dirp) {
  int fd = dirp->__fc_dir_id;
  int res = __mkfs_check_fd_dir_ok (fd); // handle __TIS_MKFS_NO_ERR
  if (res != 0)
    return res;
  return dirp->__fc_dir_position;
}
#ifndef __TIS_USER_TELLDIR
long telldir(DIR *dirp)
{ return __mkfs_telldir(dirp); }
#endif // __TIS_USER_TELLDIR

void __mkfs_rewinddir (DIR *dirp) {
  // no error detection (no returned value)
  dirp->__fc_dir_position = 0;
}
#ifndef __TIS_USER_REWINDDIR
void rewinddir (DIR *dirp)
{ __mkfs_rewinddir(dirp); }
#endif // __TIS_USER_REWINDDIR

void __mkfs_seekdir (DIR *dirp, long pos) {
  // no error detection (no returned value)
  dirp->__fc_dir_position = pos;
}
#ifndef __TIS_USER_SEEKDIR
void seekdir (DIR *dirp, long pos)
{ __mkfs_seekdir(dirp, pos); }
#endif // __TIS_USER_SEEKDIR

struct dirent *__mkfs_readdir (DIR * restrict dirp) {
  int fd = dirp->__fc_dir_id;
  int res = __mkfs_check_fd_dir_ok (fd); // handle __TIS_MKFS_NO_ERR
  if (res != 0)
    return NULL;
  struct dirent ** dirs = dirp->__fc_dir_entries;
  if (dirs[dirp->__fc_dir_position] == NULL)
    return NULL;
  return dirs[dirp->__fc_dir_position++];
}
#ifndef __TIS_USER_READDIR
struct dirent *readdir (DIR * restrict dirp)
{ return __mkfs_readdir(dirp); }
#endif // __TIS_USER_READDIR

int close_dir (int fd) {
  __mkfs_dir_info * dir = __mkfs_get_dir_info (fd);
  if (dir == NULL) {
    return -1;
  }
  dir->__fc_dir_inode = NULL;
  __mkfs_file_desc[fd].__mkfs_fd_kind = 0;
  return 0;
}

int __mkfs_closedir(DIR * restrict dirp) {
  return close_dir (dirp->__fc_dir_id);
  return 0;
}
#ifndef __TIS_USER_CLOSEDIR
int closedir(DIR * restrict dirp)
{ return __mkfs_closedir(dirp); }
#endif // __TIS_USER_CLOSEDIR

//==============================================================================
// About pipes
//==============================================================================

int __mkfs_pipe2(int pipefd[2], int flags) {
  int fd = get_next_file_desc (); // handle __TIS_MKFS_NO_ERR
  if (fd == -1)
    return fd;
  int mode = S_IFIFO | S_IRUSR | S_IWUSR;
  struct stat * st = mk_inode (mode);

  struct __mkfs_fs_file *ptr = calloc (1, sizeof(struct __mkfs_fs_file));
#ifndef __TIS_MKFS_NO_ERR
  if (!ptr) {
    tis_make_unknown((void*)&errno, sizeof errno);
    return -1;
  }
#else
  //@ assert tis_mkfs_pipe2_calloc_ok: ptr != \null;
#endif // __TIS_MKFS_NO_ERR
  ptr->__mkfs_stat = st;
  int ret = open_fd (fd, S_IFIFO, flags | O_RDONLY, NULL, ptr);
  if (ret != 0)
    return ret;
  pipefd[0] = fd;
  fd = get_next_file_desc ();
  if (fd == -1)
    return fd;
  flags |= __tis_translate_mode_string ("w");
  ptr = calloc (1, sizeof(struct __mkfs_fs_file));
#ifndef __TIS_MKFS_NO_ERR
  if (!ptr) {
    tis_make_unknown((void*)&errno, sizeof errno);
    return -1;
  }
#else
  //@ assert tis_mkfs_pipe2_calloc_ok_2: ptr != \null;
#endif // __TIS_MKFS_NO_ERR
  ptr->__mkfs_stat = st;
  ret = open_fd (fd, S_IFIFO, flags, NULL, ptr);
  if (ret != 0)
    return ret;
  pipefd[1] = fd;
  return 0;
}
#ifndef __TIS_USER_PIPE2
int pipe2(int pipefd[2], int flags)
{ return __mkfs_pipe2(pipefd, flags); }
#endif // __TIS_USER_PIPE2

int __mkfs_pipe(int pipefd[2]) {
  return pipe2 (pipefd, 0);
}
#ifndef __TIS_USER_PIPE
int pipe(int pipefd[2])
{ return __mkfs_pipe(pipefd); }
#endif // __TIS_USER_PIPE

static int close_fifo (int fd) {
  __mkfs_file_info * file_info = __mkfs_get_file_info (fd);
  int res = close_file (fd);
  if (res == 0) {
    free (file_info->__mkfs_file);
    file_info->__mkfs_file = NULL;
  }
  return res;
}

//==============================================================================
// About sockets
//==============================================================================

int __mkfs_socket(int domain, int type, int protocol) {
  int fd = get_next_file_desc (); // handle __TIS_MKFS_NO_ERR
  if (fd != -1) {
    int idx = fd; // TODO: use a counter
    __mkfs_file_desc[fd].__mkfs_fd_kind = S_IFSOCK;
    __mkfs_file_desc[fd].__mkfs_fd_index = idx;

    __mkfs_socket_info * socket = __mkfs_get_socket_info (fd);
    socket->__mkfs_sock_addr = NULL;
    socket->__mkfs_sock_addrlen = 0;
    socket->__mkfs_sock_domain = domain;
    socket->__mkfs_sock_type = type;
    socket->__mkfs_sock_protocol = protocol;
    // socket->__mkfs_sock_stat = TODO ?
  }
  return fd;
}
#ifndef __TIS_USER_SOCKET
int socket(int domain, int type, int protocol)
{ return __mkfs_socket(domain, type, protocol); }
#endif // __TIS_USER_SOCKET

int __mkfs_accept(int sockfd, struct sockaddr *addr, socklen_t *addrlen) {
  int ret = __mkfs_check_fd_socket_ok(sockfd); // handle __TIS_MKFS_NO_ERR
  if (ret != 0)
    return ret;
  int fd = get_next_file_desc(); // handle __TIS_MKFS_NO_ERR
  if (fd != -1) {
    int idx = fd;
    __mkfs_file_desc[fd].__mkfs_fd_kind = S_IFSOCK;
    __mkfs_file_desc[fd].__mkfs_fd_index = idx;

    struct __mkfs_socket * socket = __mkfs_get_socket_info (sockfd);
    struct __mkfs_socket * new_socket = __mkfs_get_socket_info (fd);

    new_socket->__mkfs_sock_addr = malloc(socket->__mkfs_sock_addrlen);
    new_socket->__mkfs_sock_addrlen = socket->__mkfs_sock_addrlen;
    new_socket->__mkfs_sock_domain = socket->__mkfs_sock_domain;
    new_socket->__mkfs_sock_type = socket->__mkfs_sock_type;
    new_socket->__mkfs_sock_protocol = socket->__mkfs_sock_protocol;
    // new_socket->__mkfs_sock_stat = TODO ?
    tis_make_unknown((char*)new_socket->__mkfs_sock_addr,
        new_socket->__mkfs_sock_addrlen);
    if (addr != NULL) {
      socklen_t len;
      if (*addrlen < new_socket->__mkfs_sock_addrlen)
        len = *addrlen;
      else
        len = new_socket->__mkfs_sock_addrlen;
      *addrlen = len;
      memcpy(addr, new_socket->__mkfs_sock_addr, len);
    }
  }
  return fd;
}
#ifndef __TIS_USER_SOCKET
int accept(int sockfd, struct sockaddr *addr, socklen_t *addrlen)
{ return __mkfs_accept(sockfd, addr, addrlen); }
#endif // __TIS_USER_SOCKET

int __mkfs_bind(int fd, const struct sockaddr * addr, socklen_t len) {
  RETURN_RANDOM_ERROR (-1);
  struct __mkfs_socket * socket = __mkfs_get_socket_info (fd);
  if (socket->__mkfs_sock_addr != NULL) {
    errno = EINVAL;
    return -1;
  }
  socket->__mkfs_sock_addr = malloc(len);
  memcpy(socket->__mkfs_sock_addr, addr, len);
  socket->__mkfs_sock_addrlen = len;
  return 0;
}
#ifndef __TIS_USER_BIND
int bind(int fd, const struct sockaddr * addr, socklen_t len)
{ return __mkfs_bind(fd, addr, len); }
#endif // __TIS_USER_BIND

int __mkfs_connect(int fd, const struct sockaddr * addr, socklen_t len) {
  return bind (fd, addr, len); // handle __TIS_MKFS_NO_ERR
}
#ifndef __TIS_USER_CONNECT
int connect(int fd, const struct sockaddr * addr, socklen_t len)
{ return __mkfs_connect(fd, addr, len); }
#endif // __TIS_USER_CONNECT

int __mkfs_getsockname(int fd, struct sockaddr *addr, socklen_t *addrlen) {
  int ret = __mkfs_check_fd_socket_ok (fd); // handle __TIS_MKFS_NO_ERR
  if (ret != 0)
    return ret;
  struct __mkfs_socket * socket = __mkfs_get_socket_info (fd);
  socklen_t len; /* minimum of *addrlen and __mkfs_sock_addrlen */
  if (*addrlen < socket->__mkfs_sock_addrlen)
    len = *addrlen;
  else
    len = socket->__mkfs_sock_addrlen;
  *addrlen = socket->__mkfs_sock_addrlen;
  memcpy(addr, socket->__mkfs_sock_addr, len);
  return 0;
}
#ifndef __TIS_USER_GETSOCKETNAME
int getsockname(int fd, struct sockaddr *addr, socklen_t *addrlen)
{ return __mkfs_getsockname(fd, addr, addrlen); }
#endif // __TIS_USER_GETSOCKETNAME

ssize_t __mkfs_recv (int fd, void *buf, size_t len, int flags) {
  int ret = __mkfs_check_fd_socket_ok (fd); // handle __TIS_MKFS_NO_ERR
  if (ret != 0)
    return ret;

  int n = tis_interval (1, len);
  tis_make_unknown ((char*)buf, n);
  return n;
}
#ifndef __TIS_USER_RECV
ssize_t recv (int fd, void *buf, size_t len, int flags)
{ return __mkfs_recv(fd, buf, len, flags); }
#endif // __TIS_USER_RECV

ssize_t __mkfs_recvfrom (int fd, void *buf, size_t len, int flags,
    struct sockaddr *src_addr, socklen_t *addrlen) {
  int n = recv (fd, buf, len, flags); // handle __TIS_MKFS_NO_ERR
  if (n != -1) {
    int r = getsockname (fd, src_addr, addrlen);
    return r == -1 ? -1 : n;
  }
  return -1;
}
#ifndef __TIS_USER_RECVFROM
ssize_t recvfrom (int fd, void *buf, size_t len, int flags,
    struct sockaddr *src_addr, socklen_t *addrlen)
{ return __mkfs_recvfrom(fd, buf, len, flags, src_addr, addrlen); }
#endif // __TIS_USER_RECVFROM

static int close_socket (int fd) {
  int ret = __mkfs_check_fd_socket_ok (fd); // handle __TIS_MKFS_NO_ERR
  if (ret != 0)
    return -1;
  __mkfs_socket_info * socket = __mkfs_get_socket_info (fd);
  if (socket == NULL)
    return -1;

  __mkfs_file_desc[fd].__mkfs_fd_kind = 0;
  if (socket->__mkfs_sock_addr != NULL)
    free(socket->__mkfs_sock_addr);
  return 0;
}
//==============================================================================

int __mkfs_close(int fd) {
  if (fd < 0 || fd >= FOPEN_MAX) {
    errno = EBADF;
    return -1;
  }
  switch ( __mkfs_file_desc[fd].__mkfs_fd_kind) {
    case 0: errno = EBADF; return -1;
    case S_IFIFO: return close_fifo (fd);
    case S_IFREG: return close_file (fd);
    case S_IFDIR: return close_dir (fd);
    case S_IFSOCK: return close_socket (fd);
    case S_IFCHR:
                   __mkfs_file_desc[fd].__mkfs_fd_kind = 0;
                   return 0;
    default: tis_make_unknown((void*)&errno, sizeof errno);
             return -1;
  }
}
#ifndef __TIS_USER_CLOSE
/* @ TODO ?
    assigns __mkfs_file_desc[fd] \from fd;
    assigns mkfs_opened_files[..] \from fd,  __mkfs_file_desc[fd];
    assigns mkfs_opened_socket[..] \from fd,  __mkfs_file_desc[fd];
    assigns __mkfs_opendir[..] \from fd,  __mkfs_file_desc[fd];
*/
int close(int fd)
{ return __mkfs_close(fd); }
#endif // __TIS_USER_CLOSE

//==============================================================================
// Remove files and directories
//==============================================================================
// set errno when \result == -1;
static int remove_file (struct __mkfs_fs_file * file) {
  RETURN_RANDOM_ERROR (-1);

  // TODO
  tis_printf ("NIY WARNING: unlinked file not being removed from dirent\n");
  //@ assert rm_file_not_dirent_mkfs_niy: WARN_NIY ;

  file->__mkfs_fullpath = NULL;
//   file->__mkfs_stat = NULL; not yet
  file->__mkfs_content = NULL;

  return 0;
}
// set errno when \result == -1;
static int remove_dir (struct __mkfs_fs_dir * dir) {

  RETURN_RANDOM_ERROR (-1);

  if (dir->__mkfs_dir_entries[2]) {
    // not empty (entry 0 is for '.' and 1 for '..')
    errno = ENOTEMPTY;
    return -1;
  }

  // This is to warn that the directory is removed from the directory table,
  // but not removed form its parent directory entries.
  //@ assert rm_dir_not_dirent_mkfs_niy: WARN_NIY ;

  dir->__mkfs_fullpath = NULL;
  dir->__mkfs_stat = NULL;
  dir->__mkfs_dir_entries = NULL;

  return 0;
}

// TODO: implement link, which requires a bit of work: we need to stop
// storing the file name in __mkfs_fs_file, since __mkfs_fs_file is really
// an inode. the file name(s) need to move into directory entries.
int __mkfs_link(const char *oldpath, const char *newpath) {
  //@ assert link_mkfs_niy: WARN_NIY ;
  return -1;
}
#ifndef __TIS_USER_LINK
int link(const char *oldpath, const char *newpath)
{ return __mkfs_link(oldpath, newpath); }
#endif // __TIS_USER_LINK

// set errno when \result == -1;
int __mkfs_unlink(const char *pathname) {
  struct __mkfs_fs_file * f = __mkfs_get_file (pathname);
  if (f == NULL) {
    errno = ENOENT;
    return -1;
  }
  return remove_file (f);
}
#ifndef __TIS_USER_UNLINK
int unlink(const char *pathname)
{ return __mkfs_unlink(pathname); }
#endif // __TIS_USER_UNLINK

// set errno when \result == -1;
ssize_t __mkfs_readlink(const char *path, char *buf, size_t bufsiz) {
  // TODO: support symbolic links
  errno = EINVAL;
  return -1;
}

#ifndef __TIS_USER_READLINK
ssize_t readlink(const char *path, char *buf, size_t bufsiz)
{ return __mkfs_readlink(path, buf, bufsiz); }
#endif // __TIS_USER_READLINK

char *__mkfs_getcwd(char *buf, size_t size) {
  static char *cwd = "/";
  if (size < 1 + strlen(cwd)) {
    errno = ERANGE;
    return NULL;
  }
  strcpy(buf, cwd);
  return buf;
}

#ifndef __TIS_USER_GETCWD
char *getcwd(char *buf, size_t size)
{ return __mkfs_getcwd(buf, size); }
#endif // __TIS_USER_GETCWD

int __mkfs_rmdir(const char *pathname) {
  struct __mkfs_fs_dir * dir = __mkfs_get_dir (pathname);
  if (dir != NULL)
    return remove_dir (dir); // handle __TIS_MKFS_NO_ERR
  tis_make_unknown((void*)&errno, sizeof errno);
  return -1;
}
#ifndef __TIS_USER_RMDIR
int rmdir(const char *pathname)
{ return __mkfs_rmdir(pathname); }
#endif // __TIS_USER_RMDIR

//==============================================================================
// mmap/munmap
//==============================================================================

#define MMAP_MAX FOPEN_MAX

typedef struct __mkfs_map {
  unsigned char * data;
  void * addr;
  size_t length;
  bool shared;
  bool need_sync;
} map;
struct __mkfs_maps {
  struct __mkfs_map maps[MMAP_MAX];
  size_t nb_used;
} maps;

static map * find_data_map (void * data) {
  //@ slevel 1000000;
  for (size_t i = 0; i < maps.nb_used; i++) {
    if (maps.maps[i].data == data)
      return maps.maps + i;
  }
  //@ slevel default;
  return NULL;
}
static map * find_addr_map (void * addr, size_t length) {
  //@ slevel 1000000;
  for (size_t i = 0; i < maps.nb_used; i++) {
    if (maps.maps[i].addr == addr && maps.maps[i].length == length)
      return maps.maps + i;
  }
  //@ slevel default;
  return NULL;
}
static void * add_map (unsigned char * data, size_t length,
    bool shared, bool need_sync) {
  if (shared) { // check if already in.
    map * map = find_data_map (data);
    if (map)
      return map->addr;
  }
  if (maps.nb_used >= MMAP_MAX) {
    errno = ENOMEM;
    return MAP_FAILED;
  }
  size_t m = maps.nb_used++;
  void * addr = malloc (length); // TODO: should be calloc (n, PAGE_SIZE)
#ifdef __TIS_MKFS_NO_ERR
  //@ assert tis_mkfs_mmap_malloc_ok: addr != \null;
#else
  if (addr == NULL) {
    errno = ENOMEM;
    return MAP_FAILED;
  }
#endif
  // TODO: use a builtin to make the location read-only is needed.
  maps.maps[m].data = data;
  maps.maps[m].addr = memcpy (addr, data, length);
  maps.maps[m].length = length;
  maps.maps[m].shared = shared;
  maps.maps[m].need_sync = need_sync;
  return addr;
}


// set errno when \result == -1;
int __mkfs_check_mmap_prot (int fd, int prot) {
  // fd needs read permission, regardless of the protection options specified.
  int ret = __mkfs_check_fd_file_ok_for_reading (fd); // handle __TIS_MKFS_NO_ERR
  if (ret != 0) return ret; // errno already set
  if (prot == PROT_NONE) {
    //@ assert mmap_prot_none_mkfs_niy: WARN_NIY ;
    return -1;
  }
  if (prot & PROT_EXEC) {
    //@ assert mmap_prot_exec_mkfs_niy: WARN_NIY ;
  }
  if (prot & PROT_WRITE) {
    ret = __mkfs_check_fd_file_ok_for_writing (fd); // handle __TIS_MKFS_NO_ERR
    return ret; // errno already set when ret != 0
  }
  else { // PROT_READ only
    return 0;
  }
}

/* This is a limited version of 'mmap' that only handle
   - offset == 0, length == size of the underlying file;
   - flags == MAP_SHARED || flags == MAP_PRIVATE
   - prot holds only PROT_READ, PROT_WRITE, or both.

   Moreover, the size of the map should be a multiple of the page size,
   with the bytes outside the file set to 0. At the moment,
   the allocated map has the same size than the file.
   This can be considered as an extra protection.

   If the content of a mapped file is modified,
   it is not propagated to the map.
   With the MAP_PRIVATE mode, it is ok since the behavior is explicitly
   unspecified.
   With the MAP_SHARED mode, it is unclear (TODO: find out what should be done)
   */
void * __mkfs_mmap(void *addr, size_t length, int prot, int flags,
    int fd, off_t offset) {
  if (flags & MAP_FIXED) {
    //@ assert mmap_map_fixed_mkfs_niy: WARN_NIY ;
    return MAP_FAILED;
  }
  // when flags does not hold MAP_FIXED,
  // addr is only a hint, so we can ignore it.
  if (offset != 0) {
    //@ assert mmap_offset_mkfs_niy: WARN_NIY ;
    return MAP_FAILED;
  }

  __mkfs_file_info * file_info = __mkfs_get_file_info (fd);
  struct stat * st = file_info->__mkfs_file->__mkfs_stat;
  if (length != st->st_size) {
    //@ assert mmap_length_mkfs_niy: WARN_NIY ;
    return MAP_FAILED;
  }

  if (__mkfs_check_mmap_prot (fd, prot) != 0) {
    return MAP_FAILED;
  }

  if (flags & MAP_SHARED == flags & MAP_PRIVATE) {
    // both on or both off : forbiden
    errno = EINVAL;
    return MAP_FAILED;
  }
  if (flags != flags & (MAP_SHARED | MAP_PRIVATE)) {
    //@ assert mmap_other_flags_mkfs_niy: WARN_NIY ;
  }

  RETURN_RANDOM_ERROR (MAP_FAILED);

  if (flags & MAP_SHARED) {
    bool writable = prot&PROT_WRITE;
    return add_map (file_info->__mkfs_file->__mkfs_data, length, true, writable);
  }
  else { // (flags & MAP_PRIVATE)
    return add_map (file_info->__mkfs_file->__mkfs_data, length, false, false);
  }
}

#ifndef __TIS_USER_MMAP
void *mmap(void *addr, size_t length, int prot, int flags,
    int fd, off_t offset) {
  return __mkfs_mmap(addr, length, prot, flags, fd, offset);
}
#endif

//@ requires msync_no_need_sync: map->need_sync;
static void msync_map_to_file (map * map) {
  memcpy (map->data, map->addr, map->length);
}

/* munmap() deletes the mappings for the specified address range,
   i.e. unmap all the pages containing a part of addr[0..length].
   The man page says is normally not an error if the indicated range
   does not contain any mapped pages, but POSIX seems to enforce that
   (addr, length) has to come from a previous `mmap` call,
   so do we here. */
int __mkfs_munmap(void *addr, size_t length) {
  RETURN_RANDOM_ERROR (-1);
  map * map = find_addr_map (addr, length);
  if (map) {
    // TODO: call msync(MS_SYNC) when required (ie MAP_SHARED+PROT_WRITE)
    if (map->need_sync)
      msync_map_to_file (map);
    free (map->addr);
    map->data = NULL; map->addr = NULL; map->length = 0;
    // maps.maps[] is not packed and maps.nb_used in not decreased here
    // on purpose to avoid using the same element for different purposes,
    // which may lead to imprecision in the analyses.
    return 0;
  }
  else {
    return -1;
  }
}

#ifndef __TIS_USER_MUNMAP
int munmap(void *addr, size_t length) {
  return __mkfs_munmap(addr, length);
}
#endif

#ifndef __TIS_USER_MSYNC
int msync(void *addr, size_t length, int flags) {
  if ((flags & MS_ASYNC) == (flags & MS_SYNC)) {
    // both on or both off : forbiden
    errno = EINVAL;
    return -1;
  }
  if (flags != flags & (MS_ASYNC & MS_SYNC & MS_INVALIDATE)) {
    errno = EINVAL;
    return -1;
  }
  if (flags & MS_INVALIDATE) {
    //@ assert msync_invalidate_mkfs_niy: \false;
  }

  map * map = find_addr_map (addr, length);
  if (map) {
    // flags already verified above.
    msync_map_to_file (map);
    return 0;
  }
  else {
    errno = ENOMEM;
    return -1;
  }
}
#endif

//==============================================================================
// fprintf familly
//==============================================================================

int vfprintf(FILE *__restrict __stream, const char *__restrict __format,
             va_list __arg) {
  int r;
  char buf[BUFSIZ];
  r = vsnprintf (buf, BUFSIZ, __format, __arg);
  if (r > 0) {
    int fd = __stream->__fc_file_desc;
    ssize_t wr = write (fd, buf, r);
    if (wr != r)
      return -1;
  }
  return r;
}

int fprintf(FILE *__restrict __stream, const char *__restrict __format, ...) {
  int r;
  va_list ap;
  va_start(ap, __format);
  r = vfprintf (__stream, __format, ap);
  va_end(ap);
  return r;
}

int vprintf(const char *__restrict __format, va_list __arg) {
  return vfprintf (stdout, __format, __arg);
}

int printf(const char *__restrict __format, ...) {
  int r;
  va_list ap;
  va_start(ap, __format);
  r = vfprintf (stdout, __format, ap);
  va_end(ap);
  return r;
}

//==============================================================================
// END.
//==============================================================================
