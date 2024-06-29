#!/usr/bin/env perl
use strict;
use warnings;
use Path::Tiny;

my $prelude = <<'END_PRELUDE';
Require Export cbpv.common.effects cbpv.common.coeffects cbpv.autosubst2.fintype.
END_PRELUDE

my $prologue = <<'END_PROLOGUE';
END_PROLOGUE

my $CBPV_syntax_path = path($ARGV[0]);


my $CBPV_syntax = join('',map { (my $s = $_) =~ s/^(Hint|Instance)/#[export]$1/; $s } grep(!/^Require Export/,$CBPV_syntax_path->lines_utf8));

$CBPV_syntax_path->spew_utf8($prelude,$CBPV_syntax,$prologue);

