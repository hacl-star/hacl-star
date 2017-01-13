#if defined(__linux__)

#include <sys/stat.h>
#include <errno.h>
#include <fcntl.h>
#include <unistd.h>
#include <string.h>

#define CPUINFO_LINE_LENGTH 128

typedef struct cpuid_flags_t {
	unsigned long processor;
	unsigned long features;
	unsigned long implementer;
	unsigned long arch;
	unsigned long variant;
	unsigned long part;
	unsigned long revision;
} cpuid_flags_t;

typedef struct cpuid_flag_table_t {
	const char *str;
	unsigned long flag;
} cpuid_flag_table_t;

static const cpuid_flag_table_t features[] = {
	{"tls ",       CPUID_TLS},
	{"aes ",       CPUID_AES},
	{"pmull ",     CPUID_PMULL},
	{"sha1 ",      CPUID_SHA1},
	{"sha2 ",      CPUID_SHA2},
	{"crc32 ",     CPUID_CRC32},
	{"iwmmxt ",    CPUID_IWMMXT},
	{"idivt ",     CPUID_IDIVT},
	{"idiva ",     CPUID_IDIVA},
	{"vfpv3d16 ",  CPUID_VFP3D16},
	{"vfpv3 ",     CPUID_VFP3},
	{"vfpv4 ",     CPUID_VFP4},
	{"neon ",      CPUID_NEON},
	{"asimd ",     CPUID_ASIMD},
	{NULL, 0}
};

/* that's an L, not a 1?? */
static const cpuid_flag_table_t processors[] = {
	{"(v6l)",      CPUID_ARMv6},
	{"(v7l)",      CPUID_ARMv7},
	{"(aarch64)",  CPUID_ARMv8},
	{NULL, 0}
};

static const cpuid_flag_table_t archs[] = {
	{"6TEJ",      CPUID_ARMv6},
	{"7",         CPUID_ARMv7},
	{"7M",        CPUID_ARMv7},
	{"AArch64",   CPUID_ARMv8},
	{NULL, 0}
};

static const char *
cpuid_ltrim(const char *line) {
	/* advance to the ':' */
	while (*line && (*line != ':'))
		line++;

	if (*line == ':')
		line++;

	/* skip whitespace */
	while (*line && ((*line == ' ') || (*line == '\t')))
		line++;

	return line;
}

static unsigned long
cpuid_parse_unsigned(const char *line) {
	unsigned long value = 0;

	if ((line[0] == '0') && (line[1] == 'x')) {
		for (line += 2; *line; line++) {
			unsigned long digit = *line;
			if ((digit - '0') < 10)
				digit -= '0';
			else if ((digit - 'A') < 16)
				digit -= ('A' - 10);
			else if ((digit - 'a') < 16)
				digit -= ('a' - 10);
			else
				return 0;
			value = (value * 16) + digit;
		}
	} else {
		for (; *line; line++) {
			unsigned long digit = *line;
			if ((digit - '0') < 10)
				digit -= '0';
			else
				return 0;
			value = (value * 10) + digit;
		}
	}

	return value;
}

static unsigned long
cpuid_scan(const char *line, const cpuid_flag_table_t *table) {
	unsigned long flags = 0;

	for (; table->str; table++) {
		if (strstr(line, table->str) != NULL)
			flags |= table->flag;
	}

	return flags;
}

/* flags: [processor, feature, arch, part] */
static void
cpuid_line_parse(const char *line, cpuid_flags_t *flags) {
	const char *trimmed = cpuid_ltrim(line);
	if (strncmp(line, "Processor", 9) == 0)
		flags->processor = cpuid_scan(trimmed, processors);
	else if (strncmp(line, "Features", 8) == 0)
		flags->features |= cpuid_scan(trimmed, features);
	else if (strncmp(line, "CPU implementer", 15) == 0)
		flags->implementer = cpuid_parse_unsigned(trimmed);
	else if (strncmp(line, "CPU architecture", 16) == 0)
		flags->arch = cpuid_scan(line + 16, archs);
	else if (strncmp(line, "CPU variant", 11) == 0)
		flags->variant = cpuid_parse_unsigned(trimmed);
	else if (strncmp(line, "CPU part", 8) == 0)
		flags->part = cpuid_parse_unsigned(trimmed);
	else if (strncmp(line, "CPU revision", 12) == 0)
		flags->revision = cpuid_parse_unsigned(trimmed);
}

static int
cpuid_line_length(char *line, int start, int end) {
	int i;
	for (i = start; i < end; i++) {
		if (line[i] == '\n') {
			line[i] = 0;
			return i - start;
		}
	}
	return -1;
}

/* parse /proc/cpuinfo in-place with no allocations */
static unsigned long
cpuid_specific_impl(void) {
	cpuid_flags_t flags = {0, 0, 0, 0, 0, 0, 0};
	int skip_to_next_line = 0;
	int incomplete_bytes = 0;

	char line[CPUINFO_LINE_LENGTH];
	int fd;

	fd = open("/proc/cpuinfo", O_RDONLY);
	if (fd < 0)
		goto cpuid_specific_impl_done;

	for (;;) {
		int cur_line_pos = 0;
		int bytes_read = read(fd, line + incomplete_bytes, CPUINFO_LINE_LENGTH - incomplete_bytes);
		int bytes_left;
		int cur_line_end;

		if (bytes_read <= 0) {
			if ((bytes_read < 0) && (errno == EINTR))
				continue;
			goto cpuid_specific_impl_done;
		}

		bytes_left = bytes_read + incomplete_bytes;
		cur_line_end = bytes_left;
		incomplete_bytes = 0;
		while (bytes_left) {
			int line_length = cpuid_line_length(line, cur_line_pos, cur_line_end);

			/* if the line extends past the buffer.. */
			if (line_length < 0) {
				if (cur_line_pos == 0) {
					/* and it's larger than our buffer, skip it */
					skip_to_next_line = 1;
				} else {
					/* otherwise copy it to the front */
					memmove(line, line + cur_line_pos, CPUINFO_LINE_LENGTH - cur_line_pos);
					incomplete_bytes = bytes_left;
					line[incomplete_bytes] = 0;
					cur_line_pos = 0;
				}

				/* break out and read more */
				break;
			}

			/* found the end of a line, are we skipping until a new line? */
			if (!skip_to_next_line)
				cpuid_line_parse(line + cur_line_pos, &flags);
			else
				skip_to_next_line = 0;

			cur_line_pos += line_length + 1;
			bytes_left -= line_length + 1;
		}
	}

cpuid_specific_impl_done:
	if (fd != -1)
		close(fd);

	/* trust processor over arch, see https://code.google.com/p/android/issues/detail?id=10812 */
	if (!flags.processor)
		flags.processor = flags.arch;

	switch (flags.implementer) {
		case 0x41: /* ARM */
			/* 0xb02: armv6k   - mpcore */
			/* 0xb36: armv6j   - arm1136j-s */
			/* 0xb56: armv6t2  - arm1156t2-s */
			/* 0xb76: armv6zk  - arm1176jz-s */
			/* 0xc05: armv7-a  - cortex-a5 */
			/* 0xc07: armv7ve  - cortex-a7 */
			/* 0xc08: armv7-a  - cortex-a8 */
			/* 0xc09: armv7-a  - cortex-a9 */
			/* 0xc0d: armv7ve  - cortex-a12 */
			/* 0xc0f: armv7ve  - cortex-a15 */
			/* 0xc14: armv7-r  - cortex-r4 */
			/* 0xc15: armv7-r  - cortex-r5 */
			/* 0xc20: armv6-m  - cortex-m0 */
			/* 0xc21: armv6-m  - cortex-m1 */
			/* 0xc23: armv7-m  - cortex-m3 */
			/* 0xc24: armv7e-m - cortex-m4 */
			/* 0xc60: armv6-m  - cortex-m0+ */
			/* 0xd03: armv8-a  - cortex-a53 */
			/* 0xd07: armv8-a  - cortex-a57 */
			break;

		case 0x51: /* Qualcomm */
			/* 0x0d4: armv7-a  - MSM8960 */
			/* 0x06f: armv7-a  - APQ8064 */

			/* work around faulty neon implementation https://code.google.com/p/chromium/issues/detail?id=341598 */
			if ((flags.arch == CPUID_ARMv7) && (flags.variant == 1) && (flags.part == 0x4d) && (flags.revision == 0))
				flags.features &= ~CPUID_NEON;
			break;

		case 0x69: /* Intel */
			break;

		default:
			break;
	}

	return CPUID_ARM | flags.processor | flags.features;
}

#endif
