#include <linux/perf_event.h>
#include <sys/syscall.h>
#include <sys/ioctl.h>
#include <unistd.h>

#include <errno.h>
#include <string.h>

#include <caml/mlvalues.h>
#include <caml/fail.h>

static int perf_event_open(struct perf_event_attr *hw_event, pid_t pid,
                           int cpu, int group_fd, unsigned long flags) {
  return syscall(SYS_perf_event_open, hw_event, pid, cpu, group_fd, flags);
}

#define NOT_INITIALIZED (-2)

int fd = NOT_INITIALIZED;

int counting = 0;

struct perf_event_attr pe;

CAMLprim value CAML_reset(value vunit) {
  if (fd == NOT_INITIALIZED) {
    pe.type = PERF_TYPE_HARDWARE;
    pe.size = sizeof(pe);
    pe.config = PERF_COUNT_HW_INSTRUCTIONS;
    pe.disabled = 1;
    pe.exclude_kernel = 1;
    pe.exclude_hv = 1;

    fd = perf_event_open(&pe, 0, -1, -1, 0);
    if (fd == -1) {
      fd = NOT_INITIALIZED;
      caml_failwith("Perf: initialisation failure.");
    }
  }

  if (counting) caml_failwith("Perf: already counting.");

  counting = 1;

  ioctl(fd, PERF_EVENT_IOC_RESET , 0);
  ioctl(fd, PERF_EVENT_IOC_ENABLE, 0);

  return vunit;
}

CAMLprim value CAML_count(value vunit) {
  if (counting == 0) caml_failwith("Perf: not counting.");

  ioctl(fd, PERF_EVENT_IOC_DISABLE, 0);
  counting = 0;

  int64_t count = 0;
  size_t n = read(fd, &count, sizeof(count));

  if (n != sizeof(count)) caml_failwith("Perf: failed to retrieve counter.");

  intnat v = Val_long(count);

  if (Long_val(v) != count) caml_failwith("Perf: counter overflow.");

  return v;
}
