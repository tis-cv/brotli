/* WARNING: file generated by tis-mkfs tool: do not modify. */
#include "__tis_mkfs.h"
#include "mkfs_filesystem.h"

/* Contents for '.' and '..' */
struct dirent fc_dir_dot = {0, 0, 0, 0, {46, 0}};
struct dirent fc_dir_dot_dot = {0, 0, 0, 0, {46, 46, 0}};

/* List of files */
struct __mkfs_fs_file __mkfs_fs_files[1];
int __mkfs_fs_files_nb = 0;
int __mkfs_fs_files_nb_max = 0;
/* List of directories */
struct __mkfs_fs_dir __mkfs_fs_dirs[1];
int __mkfs_fs_dirs_nb = 0;
int __mkfs_fs_dirs_nb_max = 0;
struct __mkfs_fs_file * __mkfs_get_file (const char *path) {
  //@ loop pragma UNROLL 0;
  for (int i = 0; i < __mkfs_fs_files_nb; i++)
    if (__mkfs_fs_files[i].__mkfs_fullpath && strcmp(__mkfs_fs_files[i].__mkfs_fullpath, path) == 0)
      return &__mkfs_fs_files[i];
  return NULL;
}
struct __mkfs_fs_dir * __mkfs_get_dir (const char *path) {
  //@ loop pragma UNROLL 0;
  for (int i = 0; i < __mkfs_fs_dirs_nb; i++)
    if (__mkfs_fs_dirs[i].__mkfs_fullpath && strcmp(__mkfs_fs_dirs[i].__mkfs_fullpath, path) == 0)
      return &__mkfs_fs_dirs[i];
  return NULL;
}
uid_t __mkfs_uid = TIS_uid;
gid_t __mkfs_gid = TIS_gid;
uid_t __mkfs_euid = TIS_euid;
gid_t __mkfs_egid = TIS_egid;


int __mkfs_next_inode = 0;

