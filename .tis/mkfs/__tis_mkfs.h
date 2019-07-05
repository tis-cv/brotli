/**************************************************************************/
/*                                                                        */
/*  This file is part of TrustInSoft Mkfs Tool.                           */
/*                                                                        */
/*    Copyright (C) 2016-2018 TrustInSoft                                 */
/*                                                                        */
/*  TrustInSoft Mkfs Tool is released under GPLv2                         */
/*                                                                        */
/**************************************************************************/

#ifndef __TIS_MKFS_H
#define __TIS_MKFS_H

#include "__fc_features.h"

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <dirent.h>
#include <fcntl.h>
#include <unistd.h>
#include <sys/socket.h>

#include <tis_builtin.h>

__BEGIN_DECLS

//==============================================================================
// Constants variables to be used in annotations without preprocessing.
//------------------------------------------------------------------------------

const int __mkfs_FOPEN_MAX = FOPEN_MAX;
const int __mkfs_R_OK = R_OK;
const int __mkfs_W_OK = W_OK;
const int __mkfs_X_OK = X_OK;
const int __mkfs_F_OK = F_OK;

const int __mkfs_O_RDWR = O_RDWR;
const int __mkfs_O_WRONLY = O_WRONLY;
const int __mkfs_O_RDONLY = O_RDONLY;
const int __mkfs_O_CREAT = O_CREAT;

//==============================================================================
// Exported types and API
//------------------------------------------------------------------------------
// About the files:
//------------------------------------------------------------------------------

typedef struct {
  fpos_t       __mkfs_position;
  char         __mkfs_error;
  char         __mkfs_eof;
  int          __mkfs_flags; // O_RDONLY 1 | O_RDWR 2 | O_WRONLY 3 + more flags.
  struct __mkfs_fs_file * __mkfs_file;
} __mkfs_file_info;

__mkfs_file_info * __mkfs_get_file_info (int fd);

//------------------------------------------------------------------------------
// About the directories:
//------------------------------------------------------------------------------

typedef DIR __mkfs_dir_info;

__mkfs_dir_info * __mkfs_get_dir_info (int fd);

//------------------------------------------------------------------------------
// About sockets:
//------------------------------------------------------------------------------
typedef struct __mkfs_socket {
  struct sockaddr *__mkfs_sock_addr;
  socklen_t __mkfs_sock_addrlen;
  int __mkfs_sock_domain;
  int __mkfs_sock_type;
  int __mkfs_sock_protocol;
  struct stat __mkfs_sock_stat;
} __mkfs_socket_info;

__mkfs_socket_info * __mkfs_get_socket_info (int fd);

//------------------------------------------------------------------------------
// Useful functions for users implementations:
// all of them return 0 if ok or set errno and return -1 otherwise.
//------------------------------------------------------------------------------
int __mkfs_check_fd_ok (int fd);

// file also includes S_IFCHR and S_IFIFO.
int __mkfs_check_fd_file_ok (int fd);
int __mkfs_check_fd_file_ok_for_reading (int fd);
int __mkfs_check_fd_file_ok_for_writing (int fd);

int __mkfs_check_fd_dir_ok (int fd);
int __mkfs_check_fd_socket_ok (int fd);

int __mkfs_seekable (int fd);

//==============================================================================
// Declaration from generated file.
//------------------------------------------------------------------------------

struct __mkfs_fs_file {
  char *__mkfs_fullpath; // not needed and shouldn't be here (useful for user?)
  struct stat * __mkfs_stat;
  unsigned char * (*__mkfs_content) (void);
  unsigned char * __mkfs_data;
};

extern struct __mkfs_fs_file __mkfs_fs_stdin;

struct __mkfs_fs_dir {
  char *__mkfs_fullpath;
  struct stat * __mkfs_stat;
  struct dirent ** __mkfs_dir_entries;
};

extern struct __mkfs_fs_file * __mkfs_get_file (const char *path);
extern struct __mkfs_fs_dir * __mkfs_get_dir (const char *path);
extern char * __mkfs_get_stdin_data (void);

extern struct __mkfs_fs_file __mkfs_fs_files[];
extern int __mkfs_fs_files_nb, __mkfs_fs_files_nb_max;

extern struct __mkfs_fs_dir __mkfs_fs_dirs[];
extern int __mkfs_fs_dirs_nb, __mkfs_fs_dirs_nb_max;

extern uid_t __mkfs_uid;
extern uid_t __mkfs_gid;
extern uid_t __mkfs_euid;
extern uid_t __mkfs_egid;

extern int __mkfs_next_inode;
extern int __mkfs_default_inode_size;

//==============================================================================

#ifndef __TIS_MKFS_BLKSIZE
#define __TIS_MKFS_BLKSIZE 512
#endif

#ifndef __TIS_MKFS_ST_DEV
#define __TIS_MKFS_ST_DEV 88
#endif

//==============================================================================

__END_DECLS

#endif
//==============================================================================
