use v5.14;
use warnings;

open my $h, "<" => "newHopeNTT.c" or die "Cannot open file: $!";
open my $out, ">" => "newHopeNTT_debug.c" or die "Cannot open file: $!";
say $out "#include <inttypes.h>";
say $out "#include <stdio.h>";
while (<$h>) {
  print $out $_;
  if (/^\s*A\[(\d)+\]\s*=\s*/) {
    say $out qq{  printf("%" PRIu16 "\\n", A[$1]);};
  }
}
say "done";
close $out;
say "out closed";
close $h;
say "h closed";
