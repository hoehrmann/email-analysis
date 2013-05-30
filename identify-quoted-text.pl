#!perl -w
#####################################################################
# Exploratory e-mail analysis utility for research purposes only.
#####################################################################
use Modern::Perl;
use Algorithm::Diff::XS;
use Statistics::Basic qw/median stddev avg/;
use Mail::Mbox::MessageParser;
use MIME::Parser;
use MIME::Parser::Reader;
use Mail::Field;
use Mail::Field::AddrList;
use Encode;
use HTML::Entities;
use URI::Escape;
use YAML::XS;
use autodie;
use List::Util qw/sum min max/;
use Statistics::Basic::Correlation qw//;
use Date::Language qw//;
use Date::Format qw//;
use Date::Parse qw//;
use Acme::IEnumerable;
use List::OrderBy;

use Storable qw//;
use Compress::Zlib qw//; 

#####################################################################
# Environment configuration
#####################################################################
binmode STDOUT;

#####################################################################
# Command line argument processing
#####################################################################
my $mbox_path = $ARGV[0] // die "Usage: $0 example.mbox\n";

#####################################################################
# Workaround for what seems to be a Mail::Mbox::MessageParser bug
#####################################################################
BEGIN {
  # avoid annoying warning
  local $Mail::Mbox::MessageParser::OLDSTDERR = undef;
}

#####################################################################
# Deflate wrappers for Storable functions
#####################################################################
sub inflate_z {
  my ($deflated) = @_;
  my ($i, $status) = Compress::Zlib::inflateInit();
  my ($out, $status2) = $i->inflate("$deflated");
  return $out;
}

sub deflate_z {
  my ($inflated) = @_;
  my ($d, $status) = Compress::Zlib::deflateInit() ;
  my ($out, $status2) = $d->deflate($inflated);
  my ($out2, $status3) = $d->flush;
  return "$out$out2";
}

sub freeze_z {
  my ($object) = @_;
  return deflate_z(Storable::freeze( $object ));
}

sub thaw_z {
  my ($deflated) = @_;
  return Storable::thaw(inflate_z( $deflated ));
}

#####################################################################
# Extract plain text from MIME::Entity objects
#####################################################################
sub get_text_plain {

  # Shouldn't there be a module for this?

  # TODO: There should be some additional markup recording which
  # parts come from a format=flowed document.

  # TODO: This should of course process nested parts recursively

  my $original = shift;
  my $e        = $original;
  my @plain;

  if ($e->effective_type eq 'text/plain') {
    push @plain, $e;

  } elsif ($e->effective_type eq 'multipart/alternative') {
    push @plain,
      [ reverse grep { $_->effective_type eq 'text/plain' }
        $e->parts ]->[0]
      if $e->parts;
  } elsif ($e->effective_type eq 'multipart/mixed') {
    push @plain,
      grep { $_->effective_type eq 'text/plain' } $e->parts;
  } elsif ($e->effective_type eq 'multipart/signed') {
    push @plain,
      [ reverse grep { $_->effective_type eq 'text/plain' }
        $e->parts ]->[0]
      if $e->parts;
  } else {
    warn "Don't know how to extract plain text from "
      . $e->effective_type
      . " messages";
  }

  return join '', map {
    my $encoded      = $_->bodyhandle->as_string;
    my $content_type = $_->get('Content-Type');
    if (defined $content_type) {
      my $field = Mail::Field->new('Content-Type', $content_type);
      my $charset = $field->charset;
      if (defined $charset) {
        my $decoded = Encode::decode($charset, $encoded, 1);
        $encoded = Encode::encode_utf8($decoded);
      }
    }
    $encoded;
  } @plain;
}

#####################################################################
# ...
#####################################################################
sub Local::Word::parent {
  my $self = shift;
  my $enum = $self->{enum}{parent_words};
  use Carp;
  Carp::confess unless defined $self->{index_in_parent};
  $enum->element_at($self->{index_in_parent});
}

sub Local::Word::following_or_self_f {
  my $self = shift;
  my $enum = $self->{enum}{child_words_f};
  warn unless defined $self->{index_f};
#  return $enum->take_while(sub { 0 })
#    unless defined $self->{index_f};
  return $enum->skip($self->{index_f});
}

sub Local::Word::following_or_self {
  my $self = shift;
  my $enum = $self->{enum}{child_words};
  return $enum->take_while(sub { 0 })
    unless defined $self->{index};
  return $enum->skip($self->{index});
}

sub Local::Word::following_f {
  my $self = shift;
  my $enum = $self->{enum}{child_words_f};
  return $enum->take_while(sub { 0 })
    unless defined $self->{index_f};
  return $enum->skip($self->{index_f} + 1);
}

sub Local::Word::following {
  my $self = shift;
  my $enum = $self->{enum}{child_words};
  return $enum->take_while(sub { 0 })
    unless defined $self->{index};
  return $enum->skip($self->{index} + 1);
}

sub Local::Word::preceding_f {
  my $self = shift;
  my $enum = $self->{enum}{child_words_f};
  return $enum->take_while(sub { 0 })
    unless defined $self->{index_f};
  return $enum->take($self->{index_f})->reverse();
}

sub Local::Word::preceding_or_self_f {
  my $self = shift;
  my $enum = $self->{enum}{child_words_f};
  return $enum->take_while(sub { 0 })
    unless defined $self->{index_f};
  return $enum->take($self->{index_f} + 1)->reverse();
}

sub Local::Word::pdist {
  my $self = shift;
  $self->parent->{index_f} - $self->{index_f}
}

sub Local::Word::preceding_line_f {
  my ($self) = @_;
  $self
    ->preceding_f
    ->skip_while(sub { $_->{line} == $self->{line} })
    ->take_while(sub { $_->{line} == $self->{line} - 1 })
}

sub Local::Word::preceding_siblings_f {
  my ($self) = @_;
  $self
    ->preceding_f
    ->take_while(sub { $_->{line} == $self->{line} })
}

sub Local::Word::following_siblings_f {
  my ($self) = @_;
  $self
    ->following_f
    ->take_while(sub { $_->{line} == $self->{line} })
}

sub Local::Word::following_line_f {
  my ($self) = @_;
  $self
    ->following_f
    ->skip_while(sub { $_->{line} == $self->{line} })
    ->take_while(sub { $_->{line} == $self->{line} + 1 })
}


#####################################################################
# Turn plain text into a list of annotated tokens
#####################################################################
sub make_word_list {
  my $text  = shift;
  my @words = $text =~ /([^\W_]+|[\W_])/gs;
  my @result;
  my $line = 1;
  my $column = 1;
  my $swgt;
  for (my $ix = 0; $ix < @words; ++$ix) {
    $swgt //= $words[$ix] eq '>';
    push @result, {
      word      => $words[$ix],
      index     => $ix,
      line      => $line,
      column    => $column++,
      starts_with_gt => 0 + $swgt,
    };
    if ($words[$ix] =~ /[\r\n]/) {
      $line++;
      $column = 1;
      undef $swgt;
    }
  }
  return @result;
}

#####################################################################
# Read mbox file into memory
#####################################################################
my %mails;

open my $mbox, '<', $mbox_path;

my $reader = Mail::Mbox::MessageParser->new({
  file_handle => $mbox,
});

my $mime_parser = MIME::Parser->new;
$mime_parser->output_to_core(1);

while (my $m = $reader->read_next_email) {
  my $entity = $mime_parser->parse_data($m);

  eval {
    my $text = get_text_plain($entity);

    $text = "\n" . decode_utf8($text);
    $text =~ s/\x0d\x0a/\x0a/sg;
	$text =~ s/^\n+/\n/g;
	$text =~ s/\n+$/\n/g;

    my $get_mid = sub {
      my $s = shift;
      return $1 if defined $s and $s =~ /(<\S+?>)/;
      "";
    };

    my $head = $entity->head;
    my $mid  = $get_mid->($head->get('Message-Id'));
    my @refs = map { $get_mid->($_) } split /\s+/,
      ($head->get('References') // "");
    my $irt = $get_mid->($head->get('In-Reply-To'));
    my $parent = $irt ? $irt : $refs[-1];

    #################################################################
    # ...
    #################################################################
    my @words = make_word_list($text);
    my @words_f = grep { $_->{word} !~ /[\s>]/ } @words;

    for (my $ix = 0; $ix < @words_f; ++$ix) {
      $words_f[$ix]->{index_f} = $ix;
    }

    # ...
    $mails{$mid} = freeze_z({
      text    => $text,
      entity  => $entity,
      parent  => $parent,
      words   => \@words,
	  words_f => \@words_f,
    });
  }
}

#####################################################################
# ...
#####################################################################

sub compute_quoted_distances {
  my ($enum_cwf) = @_;
  $enum_cwf->for_each(sub {
    delete $_->{distance};
    delete $_->{distance2};
    delete $_->{qd};
  });
  my $quoted_words_f = $enum_cwf->where(sub { $_->{quoted} });
  $quoted_words_f->pairwise(sub {
    my ($this, $next) = @_;
    my $this_p = $this->parent;
    my $next_p = $next->parent;
    my $d1 = $next->{index_f} - $this->{index_f};
    my $d3 = $this->{index_f} - $next->{index_f};
    my $d2 = $next_p->{index_f} - $this_p->{index_f};
    my $d4 = $this_p->{index_f} - $next_p->{index_f};
    $next->{distance} = $d2 - $d1;
    $this->{distance2} = $d4 - $d3;
  });

  $quoted_words_f->for_each(sub {
    my $d1 = $_->{distance};
    my $d2 = $_->{distance2};
    my $qd = (defined $d1 && defined $d2)
      ? List::Util::min(abs($d2), abs($d1))
      : ($d1 // $d2);
    $_->{qd} = $qd;
  });
}

#####################################################################
# ...
#####################################################################
sub enum_matches_sequence {
  my ($enum, @subs) = @_;
  my $base = $enum->new;
  while (@subs) {
    my $item = $base->();
    return unless ref $item;
    my $code = shift @subs;
    local $_ = $$item;
    return unless $code->($_);
  }
  "Huston, we've got a match!"
}

#####################################################################
# ...
#####################################################################
sub downgrade_to_ascii {
  my $string = shift;
  state $char_map = {
    "\x{2018}" => "'",
    "\x{2019}" => "'",
    "\x{0027}" => "'",
    "\x{0060}" => "'",
    "\x{00B4}" => "'",
    "\x{201C}" => '"',
    "\x{201D}" => '"',
    "\x{0022}" => '"',
    "\x{002D}" => '-',
    "\x{2012}" => '-',
    "\x{2013}" => '-',
    "\x{2014}" => '-',
    "\x{2022}" => '*',
    "\x{00B7}" => '*',
    "\x{006F}" => '*',
  };
  return join '', map { $char_map->{$_} // $_ } split//, $string;
}

#####################################################################
# ...
#####################################################################
sub calculate_trigrams {
  my ($enum_cwf, $enum_pwf) = @_;

  my %trigrams_parent;
  $enum_pwf->each_cons(3, sub {
    my $key = join ' ', map { $_->{word} } @_;
    push @{ $trigrams_parent{$key} }, $_[0]->{index_f};
  });

  my %trigrams_child;
  $enum_cwf->each_cons(3, sub {
    my $key = join ' ', map { $_->{word} } @_;
#    push @{ $trigrams_child{$key} }, $_[0]->{index_f};

    for (@{ $trigrams_parent{$key} }) {
      # TODO: betterify
      if ($_[0]->{index_f} > 0) {
        # Immediately preceding
        $_[0]->{trigrams_f}{$_} = $enum_cwf
          ->element_at($_[0]->{index_f} - 1)
          ->{trigrams_f}{$_ - 1};
      }
      $_[0]->{trigrams_f}{$_}++;
    }
  });

  $enum_cwf->for_each(sub {
    my $max = List::Util::max(values %{ $_->{trigrams_f} });
    $_->{trigrams_max_f} = $max // 0;
  });
}

#####################################################################
# ...
#####################################################################
sub prefix_tree {
  my $child_words = shift;
  my %lines;
  push @{ $lines{$_->{line}} }, $_ for @$child_words;

  my $root = bless {
    next => 0,
    children => [values %lines],
  }, 'Local::Node';

  my @todo = $root;
  my %members;
  while (@todo) {
    my $current = pop @todo;
    my %h;
    my @u;
    for (@{ $current->{children} }) {
      if ($current->{next} >= @$_) {
        push @u, $_;
      } else {
        my $next = $_->[ $current->{next} ];
        push @{ $h{ $next->{word} } }, $_;
      }
    }
    $current->{children} = [];
    for (values %h) {
      my $node = bless {
        next => $current->{next} + 1,
        children => $_,
      }, 'Local::Node';

	  if (@$_ > 1) {
  	    push @{ $members{$node} }, @$_;
        push @{ $current->{children} }, $node;
        push @todo, $node;
	  } else {
        push @{ $current->{children} }, $_;
	  }
    }
    push @{ $current->{children} }, @u;
  }

  return $root unless wantarray;

  my @stack = ($root);
  my @flat;
  while (@stack) {
    my $current = pop @stack;
    if (UNIVERSAL::isa($current, 'Local::Node')) {
      my $string;
      
      $string = join'',
        $members{$current}->[0][0]
          ->following_or_self
          ->take($current->{next})
          ->select(sub { $_->{word} })
          ->to_perl
        if $members{$current};

      push @flat, {
        next => $current->{next},
        members => $members{$current},
        string => $string,
      };
      push @stack, @{ $current->{children} };
    }
  }
  shift @flat;
  return @flat;
}

#####################################################################
# ...
#####################################################################
while (my ($mid, $frozen_z) = each %mails) {
  process_mail($mid);
}

#####################################################################
# ...
#####################################################################
sub process_mail {
  my ($mid) = @_;

  state $seen_mid = {};
  return if $seen_mid->{$mid}++;

  my $frozen_z = $mails{$mid};

  warn "$mid\n";

  my $obj = thaw_z($frozen_z);
  my @child_words = @{ $obj->{words} };
  my @child_words_f = @{ $obj->{words_f} };

  return unless defined $obj->{parent};
  return unless defined $mails{ $obj->{parent} };

  if (not $seen_mid->{ $obj->{parent} }++) {
    process_mail($obj->{parent});
  }

  my $parent_obj  = thaw_z($mails{ $obj->{parent} });
  return unless defined $parent_obj;

  my @parent_words = @{ $parent_obj->{words} };
  my @parent_words_f = @{ $parent_obj->{words_f} };

  ###################################################################
  # ...
  ###################################################################
  study $obj->{text};

  ###################################################################
  # Create enumerables from mail text words
  ###################################################################
  my $enum_cwf = Acme::IEnumerable->from_list(@child_words_f);
  my $enum_pwf = Acme::IEnumerable->from_list(@parent_words_f);
  my $enum_cw  = Acme::IEnumerable->from_list(@child_words);
  my $enum_pw  = Acme::IEnumerable->from_list(@parent_words);
  my $enums = {
    child_words_f  => $enum_cwf,
    parent_words_f => $enum_pwf,
    child_words    => $enum_cw,
    parent_words   => $enum_pw,
  };

  ###################################################################
  # Install enumerators in word objects
  ###################################################################
  $enum_cw->for_each(sub {
    bless $_, 'Local::Word';
    $_->{enum} = $enums;
  });

  my $parent_enums = {
    child_words_f => $enum_pwf,
    child_words   => $enum_pw,
  };

  $enum_pw->for_each(sub {
    bless $_, 'Local::Word';
    $_->{enum} = $parent_enums;
  });

  ###################################################################
  # Build a reverse index from string offset to word object
  ###################################################################
  my %child_text_offset_to_child_word;
  my $offset = 0;
  for (@child_words) {
	for my $ix ($offset .. $offset + length($_->{word})) {
	  $child_text_offset_to_child_word{$ix} = $_;
	}
	$offset += length $_->{word};
  }

  ###################################################################
  # Find and memorize common line prefixes in most-then-longest order
  ###################################################################
  my $common_line_prefixes = Acme::IEnumerable
    ->from_list(prefix_tree(\@child_words))
    ->where(sub { $_->{string} !~ /\n/ })
    ->order_by_descending(sub { scalar @{ $_->{members} } })
    ->then_by_descending(sub { length $_->{string} });

  ###################################################################
  # ...
  ###################################################################
  my $phead = $parent_obj->{entity}->head;
  my %htok;

  do {
    no warnings qw/uninitialized once/;

    local *Mail::Field::AddrList::decoded_names = sub {
      my $self = shift;
      map { s/\W+$//r } # workaround for \b limitations
      map { s/^["']|["']$//gr }
      map { Encode::decode('mime-header', $_) }
      map { $_->name, $_->phrase, $_->comment } $self->addr_list
    };

    my $field_to = Mail::Field->new('To' => $phead->get('To'));
    $htok{$_} = 'to_addr' for $field_to->addresses;
    $htok{$_} = 'to_name' for $field_to->decoded_names;

    my $field_cc = Mail::Field->new('Cc' => $phead->get('Cc'));
    $htok{$_} = 'cc_addr' for $field_cc->addresses;
    $htok{$_} = 'cc_name' for $field_cc->decoded_names;

    my $field_from = Mail::Field->new('From' => $phead->get('From'));
    $htok{$_} = 'from_addr' for $field_from->addresses;
    $htok{$_} = 'from_name' for $field_from->decoded_names;

    my $field_snd = Mail::Field->new('Sender' => ($phead->get('Sender') // 'ietf-bounces@ietf.org'));
    $htok{$_} = 'sender_addr' for $field_snd->addresses;
    $htok{$_} = 'sender_name' for $field_snd->decoded_names;
  };

  delete $htok{''};

  use YAML::XS;
  warn Dump \%htok;

  my $re_htok = join '|',
    map { sprintf '((?<=\b)%s(?=\b))', quotemeta }
    order_by_desc { length } keys %htok;

  ####
  my $simpler_text = $obj->{text};
  while ($simpler_text =~ s/^(\s*)[>]/$1 /gm) {
  }
  $simpler_text =~ s/\s/ /g;

  if (length $obj->{text} != length $simpler_text) {
    Carp::confess;
  }
  ####

  while ($simpler_text =~ /$re_htok/ipg) {
    my $match_from = $-[0];
    my $match_to   = $+[0];
    my $type = $htok{ ${^MATCH} }; # TODO: this should be case-insensitive
    for my $ix ($match_from .. $match_to - 1) {
      $child_text_offset_to_child_word{$ix}->{"is_attr"} = "head_$type";
    }
  }

  ###################################################################
  # Identify fragments of the parent's Date header in the child
  ###################################################################
  my $parent_date_string = $parent_obj->{entity}->head->get('Date');
  my $child_date_string = $obj->{entity}->head->get('Date');
  my $parent_timestamp_utc = Date::Parse::str2time($parent_date_string);
  my $parent_zone_seconds = (Date::Parse::strptime($parent_date_string))[6];
  my $child_zone_seconds = (Date::Parse::strptime($child_date_string))[6];
  my $parent_timestamp_adj = $parent_timestamp_utc + $child_zone_seconds;
  my $parent_timestamp_own = $parent_timestamp_utc + $parent_zone_seconds;

  state $format_types = {
    '%y' => 'year',
    '%Y' => 'year',
    '%X' => 'time',
    '%x' => 'date',
    '%S' => 'seconds',
    '%R' => 'time',
    '%r' => 'time',
    '%o' => 'day',
    '%M' => 'minute',
    '%L' => 'month',
    '%m' => 'month',
    '%k' => 'hour',
    '%l' => 'hour',
    '%H' => 'hour',
    '%I' => 'hour',
    '%h' => 'month',
    '%d' => 'day',
    '%e' => 'day',
    '%b' => 'month',
    '%B' => 'month',
    '%A' => 'day',
    '%a' => 'day',
    '%p' => 'pm',
  };

  my %tokens;
  for my $lang ('English') {
    my $fmt = Date::Language->new($lang);
    for my $stamp ($parent_timestamp_own, $parent_timestamp_adj) {
      while (my ($k, $v) = each %$format_types) {
        my $s = $fmt->time2str($k, $stamp, 'UTC');
        $tokens{ $s } = $v;
        $s =~ s/^\s+|\s+$//g;
        $tokens{ $s } = $v;
      }
    }
  }

  my $tz_seconds_to_string = sub {
    my $seconds = shift;
    sprintf('%+.02d%02u', ($seconds / 3600), ($seconds % 3600) / 60);
  };

  my $tz_string = $tz_seconds_to_string->($parent_zone_seconds);
  $tokens{substr($tz_string, 1, 4)} = 'tz';

  my $re = join '|',
    map { sprintf '((?<=\b)%s(?=\b))', quotemeta($_) }
    order_by_desc { length } keys %tokens;

  while ($obj->{text} =~ /$re/pg) {
    my $match_from = $-[0];
    my $match_to   = $+[0];
    my $type = $tokens{ ${^MATCH} };
    for my $ix ($match_from .. $match_to - 1) {
      $child_text_offset_to_child_word{$ix}->{"is_attr"} = "date_$type";
    }
  }

  ###################################################################
  # Generic find-and-mark routine for regex application
  ###################################################################
  my $mark = sub {
    my ($re, $prop) = @_;
    for (my $counter = 1; $obj->{text} =~ /$re/g; ++$counter) {
  	  my $match_from = $-[0];
	  my $match_to   = $+[0];
	  for my $ix ($match_from .. $match_to - 1) {
	    $child_text_offset_to_child_word{$ix}->{$prop} = $counter;
	  }
    }
  };

  my $mark_with_sub = sub {
    my ($re, $code) = @_;
    for (my $counter = 1; $obj->{text} =~ /$re/g; ++$counter) {
  	  my $match_from = $-[0];
	  my $match_to   = $+[0];
	  for my $ix ($match_from .. $match_to - 1) {
        my $word = $child_text_offset_to_child_word{$ix};
        local $_ = $word;
        $code->($_, $counter);
	  }
    }
  };

  ###################################################################
  # Identify words on lines starting with `>From`
  ###################################################################
  $mark->(qr/\n>From [^\n]*/, 'starts_with_gt_from');

  ###################################################################
  # Identify `...` forms
  ###################################################################
  $mark->(qr/[\[(]?([.][.][.]|\x{2026})[)\]]/, 'ellipsis');

  ###################################################################
  # Identify the value of the parent's `Subject:` header in the child
  ###################################################################
  my $subj = Encode::decode('mime-header', $phead->get('Subject'));
  $subj =~ s/\s+/ /g;
  my $subj_re = join qr/[\s>]*/, map { quotemeta } split/\s|\b/, $subj;
  $mark_with_sub->(qr/$subj_re/i, sub { $_->{is_attr} = "subject" });

  ###################################################################
  # Identify the `Message-ID` of the parent mail in the child mail
  ###################################################################
  my $msid = Encode::decode('mime-header', $phead->get('Message-Id'));
  $msid =~ s/\s+/ /g;
  $msid =~ s/^<|>$//g;
  my $msid_re = join qr/[\s>]*/, map { quotemeta } split/ /, $msid;
  $mark_with_sub->(qr/$msid_re/i, sub { $_->{is_attr} = "message_id" });

  ###################################################################
  # ...
  ###################################################################

  # Detects artificats like `www.example.com<http://www.example.com>`
  # that are generated by web mailers during HTML-to-text conversion.
  # Marks the whole sequence to support later analysis as necessary.

  my @gmunged_expressions;
  while ($obj->{text} =~ /.*<.*>.*/pgm) {
    my $temp = ${^MATCH};
    my $copy = $temp;
    $temp =~ s/[\s\*]//g;
    while ($temp =~ /(.*\W.*)<(.*)\1>/g) {
      my @gmunged = split//, "$1<$2$1>";
      my $middle_re = qr/[\s\*]*/;
      my $gmunged_re = join $middle_re, map { quotemeta } @gmunged;
      push @gmunged_expressions, $gmunged_re;
    }
  }

  $mark->($_, 'gmunged') for @gmunged_expressions;

  ###################################################################
  # ...
  ###################################################################
  my @gmunged_expressions2;
  while ($obj->{text} =~ /.*<.*>.*/pgm) {
    my $temp = ${^MATCH};
    my $copy = $temp;
    $temp =~ s/[\s\*]//g;
    while ($temp =~ /<(.*?)(.*\W.*)>\2/g) {
      my @gmunged = split//, "<$1$2>$2";
      my $middle_re = qr/[\s\*]*/;
      my $gmunged_re = join $middle_re, map { quotemeta } @gmunged;
      push @gmunged_expressions2, $gmunged_re;
    }
  }

  $mark->($_, 'gmunged') for @gmunged_expressions2;

  ###################################################################
  # ...
  ###################################################################
  $mark->(qr/<javascript:;>/, 'gmunged');

  ###################################################################
  # ...
  ###################################################################
  # TODO: still missing the form example@example.org (mailto:...)
  # for HTTP replacements like `~` => %7E missing

  ###################################################################
  # Using `sdiff` to identify quoted text.
  ###################################################################
  my @diff3 = Algorithm::Diff::sdiff(
    \@parent_words_f,
    \@child_words_f,
	sub {
      return $_[0]->{word};
    });

  for (@diff3) {
    next unless $_->[0] eq 'u';
    $_->[2]->{unmodified_in_diff} = 1;
    $_->[2]->{index_in_parent}    = $_->[1]->{index};
    $_->[2]->{index_in_parent_f}  = $_->[1]->{index_f};
  }

  $_->{quoted} = $_->{unmodified_in_diff} // 0 for @child_words;

  ###################################################################
  # ...
  ###################################################################

  my $max_rounds = 2;
  ###################################################################
  # ...
  ###################################################################
  for my $round (1 .. $max_rounds) {

  ###################################################################
  # Sanity check
  ###################################################################
  my $last_pi = -1;
  for (@child_words_f) {
    my $pi = $_->{index_in_parent};
    next unless defined $pi;
    if ($pi <= $last_pi) {
      require Carp;
      # TODO: ...
      state $once = do {
        Carp::carp "  ## Structural error in hacked diff";
      };
      $_->{bad_match} = 1;
      next;
    }
    $last_pi = $pi;
  }

  ###################################################################
  # Common suffixes among parent and child mail (e.g., list footers)
  ###################################################################

  # TODO: this should only really be applied when there is solid
  # evidence of using a quote prefix, otherwise text quoted without
  # a quote prefix would be mistaken. Also, it seems that the common
  # suffix should also be marked in the parent.

  $enum_cwf
    ->reverse
    ->zip($enum_pwf->reverse)
    ->take_while(sub { $_->[0]{word} eq $_->[1]{word} })
    ->select(sub { $_->[0] })
    ->take_while(sub { $_->{quoted} })
    ->take_while(sub { !$_->{starts_with_gt} })
    ->for_each(sub {
      delete $_->{quoted};
      delete $_->{index_in_parent};
      delete $_->{index_in_parent_f};
      $_->{common_suffix} = 1;
    });

  ###################################################################
  # ...
  ###################################################################
  my %child_words_h   = map { $_->{word}, 1 } @child_words;
  my %parent_words_h  = map { $_->{word}, 1 } @parent_words;
  $_->{not_in_parent} = 1 for grep { not $parent_words_h{$_->{word}} }
    @child_words_f;

  ###################################################################
  # ...
  ###################################################################
  compute_quoted_distances($enum_cwf);

  ###################################################################
  # ...
  ###################################################################
  my $parent_words_f = $parent_obj->{words_f};
  my $parent_words   = $parent_obj->{words};
  my $child_words_f  = $obj->{words_f};

  $_->{only_in_parent} = 1
    for grep { not $child_words_h{ $_->{word} } } @parent_words;

  my $max = 40;

  # This keeps track of something like all the objects that make up
  # the last 40 characters on this line, including their count, the
  # length, and the number of objects among them that have a certain
  # property, kind of like a queue with a sliding window. This ought
  # to be a separate class, but so far I couldn't think of a nice
  # interface for that.

  my $an = (
    sub {
      my $an;
      $an = {
        reset => sub {
          my $prop = shift;
          $an->{len}   = 0;
          $an->{count} = 0;
          $an->{elems} = [];
          $an->{prop}  = $prop;
        },
        del => sub {
          my $elems = $an->{elems};
          my $old   = shift @$elems;
          $an->{len} -= length $old->{word};
          $an->{count} -= $old->{ $an->{prop} } // 0;
        },
        add => sub {
          my $new   = shift;
          my $elems = $an->{elems};
          push @$elems, $new;
          $an->{len} += length $new->{word};
          $an->{count} += ($new->{ $an->{prop} } // 0);
          while ($an->{len} > $max) {
            last if @$elems == 1;
            $an->{del}->();
          }
          while ($elems->[0]->{line} != $elems->[-1]->{line}) {
            $an->{del}->();
          }
        },
      };
    }
  )->();

  ###################################################################
  # ...
  ###################################################################
  delete $_->{only_in_parent} for grep { length $_->{word} == 1 } @parent_words;
  delete $_->{not_in_parent} for grep { length $_->{word} == 1 } @child_words;

  $an->{reset}->('only_in_parent');
  for (@parent_words_f) {
    $an->{add}->($_);
    $_->{nearby_unquoted_before} = $an->{count};
  }

  $an->{reset}->('only_in_parent');
  for (reverse @parent_words_f) {
    $an->{add}->($_);
    $_->{nearby_unquoted_after} = $an->{count};
  }

  $an->{reset}->('not_in_parent');
  for (@child_words_f) {
    $an->{add}->($_);
    $_->{nearby_unique_before} = $an->{count};
  }

  $an->{reset}->('not_in_parent');
  for (reverse @child_words_f) {
    $an->{add}->($_);
    $_->{nearby_unique_after} = $an->{count};
  }

  ###################################################################
  # Handkamm Quoting
  ###################################################################

  ###################################################################
  #   > This line is properly quoted, and
  #   > so is this line.
  # 
  #   This is original text.
  # 
  #   And this is the continuation of the
  #   > quoted text above, lacking the ">"
  #   > at the beginning of the first line.
  ###################################################################

  $enum_cwf
    ->stack_by(sub { $_->{line} })
    ->select(sub { $_->first() })
    ->where(sub { $_->{quoted} })
    ->where(sub { $_->{starts_with_gt} })
    ->for_each(sub {
      my $r = $_;
      my $q = $r->preceding_f
        ->take_while(sub { !$_->{starts_with_gt} })
        ->take_while(sub { $_->{quoted} })
        ->take_while(sub { $_->{line} + 1 == $r->{line} })
        ->take_while(sub { $_->pdist() == $r->pdist() })
        ->to_list;

      return unless $q->count;

      # $q needs to be a whole line
      my $prev = $q->last->preceding_f->first;
      return if $prev and $prev->{line} == $q->last->{line};

      # $q must not be a whole line in the parent
      
      # TODO: this actually happens, an example in the wild is
      # CAGdtn26uX8473sxtX6v3C0ny_WLJacO_ek0pEUzYbYrvZo=RDQ@mail.gmail.com
      # unclear what to do about that...
      
      my $parent_prev = $q->last->parent->preceding_f
        ->first_or_default(undef);
      return unless $parent_prev;
      return if $parent_prev and
        $parent_prev->{line} != $q->last->parent->{line};

      $q->for_each(sub {
        $_->{kammquoted} = 1;
      });
    });

  ###################################################################
  # ...
  ###################################################################
  $enum_cwf->for_each(sub {
    my $r = $_;
    my $enum = $r->following_or_self_f;

    return unless enum_matches_sequence($enum,
      sub { $_->{quoted} },
      sub { not $_->{quoted} }, # and length $_->{word} == 1
      sub { $_->{quoted} },
    );

    my $tx = $enum->element_at(0);
    my $w1 = $tx->parent->following_f->first_or_default(undef);

    return unless defined $w1;

    my $w2 = $enum->element_at(1);

    my $quoted_prefix = quotemeta $w1->{word};

    warn $w2->{word} . "\n";

    # TODO: news:69C0294949D442C5A5FD9B3A0A939A12@gmail.com with
    # melded in parent but unmelded in grandparent and unmelded
    # in child.

    if ($w2->{word} =~ /^$quoted_prefix/) {
      my $qq = $w1->following_f->first_or_default(undef);
      if ($qq) {
        my $quoted_suffix = quotemeta $qq->{word};
        if ($w2->{word} =~ /^ $quoted_prefix $quoted_suffix $/x) {
          $w2->{weak_match} = "melded";
        }
      }
    }

    if (length $w1->{word} == 1) {
      my $ascii1 = downgrade_to_ascii($w1->{word});
      my $ascii2 = downgrade_to_ascii($w2->{word});

      if ($ascii1 eq $ascii2) {
        $w2->{weak_match} = "asciified";
      }
      elsif ($w2->{word} eq '?') {
        $w2->{weak_match} = "replacement";
      }
      else {
        $w2->{weak_match} = "other";
      }
    }
    elsif (length $w2->{word} == 1) {
      $w2->{weak_match} = "other";
    }

  });

  ###################################################################
  # Identify tokens that have been split into two while quoting them
  ###################################################################
  $enum_cwf->for_each(sub {
    my $r = $_;
    my $enum = $r->following_or_self_f;

    return unless enum_matches_sequence($enum,
      sub { $_->{quoted} },
      sub { not $_->{quoted} },
      sub { not $_->{quoted} },
      sub { $_->{quoted} },
    );

    return unless enum_matches_sequence($enum,
      sub { $_->{line} == $r->{line} },
      sub { $_->{line} == $r->{line} },
      sub { $_->{line} == $r->{line} + 1 },
      sub { $_->{line} == $r->{line} + 1 },
    );

    my $next_word_in_parent = $enum->first->parent
      ->following_f->first;

    my $p1 = $enum->element_at(1)->{word};
    my $p2 = $enum->element_at(2)->{word};

    return unless $next_word_in_parent->{word} eq "$p1$p2";

    $enum->element_at(1)->{split_inside_word} = 1;
    $enum->element_at(2)->{split_inside_word} = 1;
  });

  ###################################################################
  # ...
  ###################################################################

  {
    no warnings;

    for (@child_words) {
      my $pw = $_->{quoted} ? $_->parent : undef;
      my @score;
      push @score, $pw->{nearby_unquoted_before};
      push @score, $pw->{nearby_unquoted_after};
      push @score, $_->{nearby_unique_before};
      push @score, $_->{nearby_unique_after};
      push @score, $_->{qd};
      push @score, !$_->{starts_with_gt};

      my $thing = sum map { 0 + !!$_ } @score;

      $_->{sum_notquoted} = $thing;
      if ($thing >= 3) {
        $_->{was_sdiff_quoted} = 1
          if $_->{unmodified_in_diff};
        $_->{quoted}    = 0;
      }
    }
  }

  ###################################################################
  # ...
  ###################################################################
  my @interest2 =
    grep { not($_->{quoted} and $_->{sum_notquoted} > 1) }
    grep { not $_->{ellipsis} and not $_->{signature_marker} }
    @child_words_f;

  ###################################################################
  # ...
  ###################################################################
  $_->{swgtq} = ((!!$_->{starts_with_gt}) != (!!$_->{quoted}))
    for @interest2;

  ###################################################################
  # ...
  ###################################################################
  compute_quoted_distances($enum_cwf);

  my $redo = 0;

  my $updt = sub {
    my ($c, $p) = @$_;
    $c->{quoted} = 1;
    $c->{index_in_parent}   = $p->{index};
    $c->{index_in_parent_f} = $p->{index_f};
    $c->{omg} = 1;
    $redo = 1;
  };

  # TODO: these two should not make lines half-quoted/unquoted
  # perhaps limit them to operate on "the same line" only.

  $enum_cwf
    ->stack_by(sub { $_->{distance2} // -1 })
    ->where(sub { $_->key == 0 })
    ->select(sub { $_->first })
    ->for_each(sub {
      $_->preceding_f
        ->zip($_->parent->preceding_f)
        ->take_while(sub { $_->[0]{word} eq $_->[1]{word} })
        ->for_each($updt);
    });

  compute_quoted_distances($enum_cwf);

  $enum_cwf
    ->stack_by(sub { $_->{distance} // -1 })
    ->where(sub { $_->key == 0 })
    ->select(sub { $_->last })
    ->where(sub { defined $_->{index_in_parent} })
    ->for_each(sub {
      $_->following_f
        ->zip($_->parent->following_f)
        ->take_while(sub { $_->[0]{word} eq $_->[1]{word} })
        ->for_each($updt);
    });

  ###################################################################
  # ...
  ###################################################################
  for (@child_words) {
    # TODO: this is too eager
    delete $_->{is_attr} if $_->{quoted} or not defined $_->{index_f};;
  }

  ###################################################################
  # ...
  ###################################################################

  my $is_attribution   = sub { 0 + !!$_[0]->{is_attr} };
  my $isnt_attribution = sub { 0 + !$_[0]->{is_attr} };

  my %line_has_attribution;
  $line_has_attribution{$_} = 1 for
    $enum_cwf
      ->where($is_attribution)
      ->select(sub { $_->{line} })
      ->to_perl;

  ###################################################################
  # Attribution-like words like "From" at beginning of line
  ###################################################################
  my $attribution_head_re = 
    qr/\n[>\s]*(From|Sent|Date|To|Cc|CC|Sender|Subject
                |Importance|In|On|At|Resent-From|Resent-Date)/xs;

  while ($obj->{text} =~ /$attribution_head_re/pg) {
    my $match_from = $-[0];
    my $match_to   = $+[0];
    for my $ix ($match_from .. $match_to - 1) {
      my $word = $child_text_offset_to_child_word{$ix};
      next unless $line_has_attribution{$word->{line} + 0} or
                  $line_has_attribution{$word->{line} + 1};
      $word->{"is_attr"} = "head";
      $line_has_attribution{$word->{line}} = 1;
    }
  }

  ###################################################################
  # Attribution-like words on lines with other attribution
  ###################################################################
  my $attribution_infix_re =
    qr/\b(mailto|at|wrote|writes|On|behalf|Behalf
          |of|Of|message|Message|ext|on|EXT|by)\b/xs;

  while ($obj->{text} =~ /$attribution_infix_re/pg) {
    my $match_from = $-[0];
    my $match_to   = $+[0];
    for my $ix ($match_from .. $match_to - 1) {
      my $word = $child_text_offset_to_child_word{$ix};
      next unless $line_has_attribution{$word->{line}};
      $word->{"is_attr"} = "infix";
      $line_has_attribution{$word->{line}} = 1;
    }
  }

  ###################################################################
  # Punctuation around attribution
  ###################################################################
  while ($obj->{text} =~ /[^\p{Letter}\p{Digit}\p{Whitespace}]*/pg) {
    my $match_from = $-[0];
    my $match_to   = $+[0];
    for my $ix ($match_from .. $match_to - 1) {
      my $word = $child_text_offset_to_child_word{$ix};
      next unless $line_has_attribution{$word->{line}};
      my $p1 = $word->preceding_f->first_or_default({});
      my $p2 = $word->following_f->first_or_default({});
      next unless $is_attribution->($p1) or $is_attribution->($p2);
      $word->{"is_attr"} = "punct";
      $line_has_attribution{$word->{line}} = 1;
    }
  }

  ###################################################################
  # `----- Original Message -----` if followed by other attribution.
  ###################################################################
  while ($obj->{text} =~ /\n[\s>]*-----.*?-----\n/pg) {
    my $match_from = $-[0];
    my $match_to   = $+[0];
    for my $ix ($match_from .. $match_to - 1) {
      my $word = $child_text_offset_to_child_word{$ix};
      next unless $line_has_attribution{$word->{line} + 1} or
                  $line_has_attribution{$word->{line} + 2};
      $word->{"is_attr"} = "outlook";
      $line_has_attribution{$word->{line}} = 1;
    }
  }

  ###################################################################
  # ...
  ###################################################################

  my %interesting_lines =
  map {
    map { $_ => 1 } grep { $_ > 2 } ($_ - 1, $_, $_ + 1)
  } keys %line_has_attribution;

  $enum_cwf
    ->where(sub { $interesting_lines{ $_->{line} } })
    ->for_each(sub {
      my $a1 = $_->preceding_line_f->select($is_attribution)->average;
      my $a2 = $_->following_line_f->select($is_attribution)->average;
      my $a3 = $_->preceding_siblings_f->select($is_attribution)->average;
      my $a4 = $_->following_siblings_f->select($is_attribution)->average;
      my $sum = List::Util::sum(map { $_ // 0 } $a1, $a2, $a3, $a4);

      if ($sum < 1 and (($a3 // 0) + ($a4 // 0) < 0.5)) {
        delete $_->{is_attr};
      }
      if ($sum > 2 and not $is_attribution->($_)) {
        $_->{is_attr} = 'kernel';
      }
    });

  ###################################################################
  # ...
  ###################################################################
  my $xxx = $enum_cwf
    ->where(sub { not $_->{quoted} })
    ->where(sub { $_->{starts_with_gt} })
    ->to_list;

  if ($xxx->count > 0) {
    warn "  ## trigrams";
    calculate_trigrams($enum_cwf, $enum_pwf);
  }

  $xxx
    ->where(sub { $_->{trigrams_max_f} > 0 })
    ->for_each(sub {
      while (my ($k, $v) = each %{ $_->{trigrams_f} }) {
        next unless $v == $_->{trigrams_max_f};
        $_->{quoted} = 1;
        $_->{index_in_parent_f} = $k;
        $_->{index_in_parent} = $enum_pwf->element_at($k)->{index};
        $redo = 1;
        last;
      }
      $_->{omg} = 3;
    });

  if ($redo && $round < $max_rounds) {
    state $keep = { map { $_ => 1 } qw/
      column enum gmunged index index_f index_in_parent
      index_in_parent_f is_attr line quoted starts_with_gt
      starts_with_gt_from trigrams_f trigrams_max_f
      unmodified_in_diff word
    / };

    $enum_cwf->for_each(sub {
      foreach my $k (grep { !$keep->{$_} } keys %$_) {
        delete $_->{$k};
      }
    });
  }

  ###################################################################
  # ...
  ###################################################################
  last unless $redo;
  };

  ###################################################################
  # ...
  ###################################################################

  $enum_cwf
    ->stack_by(sub { $_->{line} })
    ->select(sub { $_->last() })
    ->where(sub { $_->{quoted} })
    ->where(sub { $_->{starts_with_gt} })
    ->for_each(sub {
      my $r = $_;
      $r->following_f
        ->take_while(sub { !$_->{starts_with_gt} })
        ->take_while(sub { $_->{quoted} })
        ->take_while(sub { $_->pdist() == $r->pdist() })
        ->for_each(sub {
          # $_->parent->{line} == $r->parent->{line}
          $_->{kammquoted} = 1;
      });
    });

  # Now, if this resulted in lines in the child that start with some-
  # thing seemingly kammquoted, but the rest of the line is not kamm-
  # quoted, then the start of the line probably also wasn't kammquoted.
  # In fact, most probably not quoted at all, and accordingly not kamm-
  # quoted. ...

  ###################################################################
  # 
  ###################################################################

  my @niebelungen = 
      grep { not $_->{starts_with_gt_from} }
      grep { not $_->{split_inside_word} }
      grep { not $_->{weak_match} }
      grep { not $_->{gmunged} }
      grep { not $_->{is_attr} }
      grep { not $_->{kammquoted} }
      grep { not $_->{ellipsis} }
      grep { $_->{word} !~ /^(mailto|http)$/ }
      grep { $_->{word} !~ /^[:*.\-_\/<>()]$/ }
      @child_words_f
  ;

  my $is_original = sub {
    my ($self) = @_;
    not $self->{quoted} and not $self->{starts_with_gt}
  };

  my $corr_sub = sub {
    Statistics::Basic::corr(
      [ map { $_->{starts_with_gt} } @niebelungen ],
      [ map { $_->{quoted} } @niebelungen ],
    )
  };

  my $corr2_sub = sub {
    Statistics::Basic::corr(
      [ map { $_->{starts_with_gt}       } grep { $_->{quoted} } @niebelungen ],
      [ map { $is_original->($_->parent) } grep { $_->{quoted} } @niebelungen ],
    );
  };

  my $corr3_sub = sub {
    Statistics::Basic::corr(
      [ map { $_->{starts_with_gt}    } grep { not $_->{quoted} or $is_original->($_->parent) } @niebelungen ],
      [ map { $_->{quoted}            } grep { not $_->{quoted} or $is_original->($_->parent) } @niebelungen ],
    );
  };

  my ($corr, $corr2, $corr3);
  my $recompute_correlations = sub {
    $corr = $corr_sub->();
    $corr2 = $corr2_sub->();
    $corr3 = $corr3_sub->();
  };

  $recompute_correlations->();

  ###################################################################
  # ...
  ###################################################################
  $enum_cwf
    ->take_while(sub { not $_->{starts_with_gt} })
    ->stack_by(sub { $_->{line} })
    ->for_each(sub {
      my $original = $_->where(sub { not $_->{quoted} })->any;
      my $attribution = $_->where(sub { $_->{is_attr} })->any;
      return unless $original and $attribution;
      $_->where(sub { $_->{quoted} })->for_each(sub {
        delete $_->{index_in_parent};
        delete $_->{index_in_parent_f};
        delete $_->{quoted};
      });
    }) if $corr > 0.5 and $corr < 1;

  $recompute_correlations->();

  ###################################################################
  # ...
  ###################################################################
  $enum_cwf
    ->reverse
    ->take_while(sub { not $_->{starts_with_gt} })
    ->take_while(sub { $_->{quoted} })
    ->for_each(sub {
      delete $_->{index_in_parent};
      delete $_->{index_in_parent_f};
      delete $_->{quoted};
    }) if $corr3 > 0.5;

  $recompute_correlations->();

  ###################################################################
  # ...
  ###################################################################


  ###################################################################
  # Print as HTML code
  ###################################################################

  state $once = do {
    print q{
	<style>

	pre:nth-of-type(odd) { background-color: #eee }
	[data-quoted] { color: #ccc; font-style: normal }
	pre { white-space: pre-wrap }
	b { font-weight: normal }

		  x[data-not_in_parent] { background-color: crimson }
/*
		  .gt_only_index_in_parent { background-color: steelblue }
		  .gt_only_same_index .gt_only_index_in_parent { background-color: transparent } 
*/
		  x[data-is_frequent] i { background-color: ivory }
		  [data-is_parent]   { background-color: honeydew }
		  [data-is_ffwrap]   { background-color: goldenrod }
		  [data-is_datetime] { background-color: darkseagreen }
		  [data-is_outlook]  { background-color: red }
		  [data-is_email_part]       { background-color: darkgoldenrod }
		  [data-common_suffix]   { background-color: deepskyblue }
		  [data-word_on_frequent_line] { background-color: lightskyblue }

		  [data-is_uri_part]         { background-color: tan }
		  [data-is_attribution_like] { background-color: lime }
		  [data-swgtq]               { background-color: black; color: white }
		  [data-swgtq][data-quoted]  { background-color: #660; color: grey }

          [data-was_sdiff_quoted]    { outline: 2px dashed lime }
          [data-omg]                 { outline: 3px solid pink }
          pre[data-gtq='1'] { display: nonex }
          [data-show='no'] { display: none }
          [data-gtq][data-gtq*="0.9"] { display: nonex }
	      [data-kammquoted], [data-kammquoted] * { background-color: BROWN !important }
          [data-split_inside_word] { background-color: YELLOW !IMPORTANT }
          [data-weak_match] { background-color: tan !IMPORTANT }
          [data-gmunged] { background-color: tan !IMPORTANT }
          [data-is_attr] { background-color: limegreen !IMPORTANT }
          [data-swgtq][data-trigrams_max_f]:not([data-quoted]) { background-color: blue !IMPORTANT }
	</style>
	};
  };

  my $mid_s = $1 if $mid =~ /<(.*)>/;
  my $mid_p = $1 if $obj->{parent} =~ /<(.*)>/;

  my $show = (($corr >= 0.96) or ($corr2 >= 0.96));

  # 
  $show = 1 unless $enum_cwf
    ->where(sub { $_->{quoted} or $_->{starts_with_gt} })
    ->any;

  if (!$show) {
    my @alternative_prefix = $common_line_prefixes
      ->where(sub { $_->{string} =~ /[^\w\s]$/ })
      ->take_while(sub {

        my $prefix = $_;
        my @lines = @{ $_->{members} };

        my %words =
          map { $_ => 1 }
          grep { defined $_->{index_f} }
          map { @$_ } @lines;
        my %is_prefix =
          map { $_ => 1 }
          grep { $_->{column} <= length $prefix->{string} }
          grep { defined $_->{index_f} }
          map { @$_ } @lines;

        my $correlation = Statistics::Basic::corr(
              [ map { $words{$_} } grep { !$is_prefix{$_} } @niebelungen ],
              [ map { $_->{quoted} } grep { !$is_prefix{$_} } @niebelungen ],
            );
        return $correlation >= 0.96;
      })
      ->take(1)
      ->to_perl;

    if (@alternative_prefix) {
      warn "\n\n ~~~~ [$_->{string}] probably quote prefix\n\n";
      $show = 1;
    } else {
      # No discernable single quoting prefix. There might be multiple,
      # like with Gnus quoting, or genuinely none. If there are no
      # lines that ...
    }
  }

  # TODO: weak matches should be counted here?
  my %parent_word_quoted_in_child = map {
    $_->{quoted} ? ($_->{index_in_parent_f} => 1) : ()
  } $enum_cwf->to_perl;

  my $percentage_of_parent_quoted = $enum_pwf->count 
    ? (keys %parent_word_quoted_in_child) / ($enum_pwf->count)
    : 0;

  my $has_black = $enum_cwf->where(sub {
    $_->{starts_with_gt} and not $_->{quoted}
  })->any;

  $show = 1 if $percentage_of_parent_quoted >= 0.96
                and $corr2 <= -0.96
                and not $has_black;

  $show = 1 if $percentage_of_parent_quoted >= 0.96
                and $corr2 eq "n/a"
                and not $has_black;

  printf "<pre data-show='%s' data-gtq='%s'><a href='http://mid.gmane.org/%s'
    >news:%s</a> (<a href='http://mid.gmane.org/%s'>parent</a>) ~~ %s ~~ %s ~~ %s ~~ %.2f\n",
    (($show) ? 'no' : 'yes'),
    encode_entities($corr),
    encode_entities(uri_escape($mid_s)),
    encode_entities($mid_s),
    encode_entities(uri_escape($mid_p)),
    encode_entities($corr),
    encode_entities($corr2),
    encode_entities($corr3),
    encode_entities($percentage_of_parent_quoted),
  ;

  print "\n";

  ###################################################################
  # ...
  ###################################################################

  for (@child_words) {
    printf "<b title='%s' ", encode_entities($_->{trigrams_max_f} // '');
    for my $k (keys %$_) {
      next if $k =~ /enum|nearby|unmodified|line|column|index|starts_with_gt\b|child|sum/;
      my $v = $_->{$k};
      next unless $v;
      printf " data-%s='%s'", encode_entities($k),
        encode_entities($v);
    }
    print ">";

    print encode_entities($_->{word});

    print "</b>" x 1;
  }
  print "</pre>";

  ###################################################################
  # ...
  ###################################################################

  for (@child_words) {
    delete $_->{enum};
  }
  $mails{$mid} = freeze_z({
    %$obj,
  });
}

Storable::nstore \%mails, 'intermediate.storable';


__END__

  if ($corr >= 0.96 or $corr2 >= 0.96) {
    # Word in `@niebelungen` on lines that do not start with `>` are most
    # likely not quoted, and marking them not quoted would boost one of
    # the correlations, or both, to `1`. For $corr2 a further implication
    # is that the seemingly quoted text from a parent's ancestor is likely
    # a signature of some kind. The closer $corr2 is to `-1`, the more ob-
    # viously does the "child" mail client not use `>` to indicate quotes.

    # ...
  }

  #
  # $corr  ~~ 1.0 <=> `>` is quote mark and no misidentified quotes
  # $corr2 ~~ 1.0 <=> `>` is quote mark and maybe misiden
  #
