package Stack;

#
# Copyright 2022 Meteo-France
# All rights reserved
# philippe.marguinaud@meteo.fr
#


use Fxtran;
use strict;
use Data::Dumper;
use Scope;

sub iniStack
{
  my ($do_jlon, $indent, $stack84, $JBLKMIN, $KGPBLKS) = @_;

  if ($stack84)
    {
      for my $size (4, 8)
        {
          $do_jlon->insertAfter (&s ("YLSTACK%U${size} = stack_u${size} (YSTACK, JBLK-$JBLKMIN+1, $KGPBLKS)"), $do_jlon->firstChild);
          $do_jlon->insertAfter (&t ("\n" . (' ' x $indent)), $do_jlon->firstChild);
          $do_jlon->insertAfter (&s ("YLSTACK%L${size} = stack_l${size} (YSTACK, JBLK-$JBLKMIN+1, $KGPBLKS)"), $do_jlon->firstChild);
          $do_jlon->insertAfter (&t ("\n" . (' ' x $indent)), $do_jlon->firstChild);
        }
    }
  else
    {
      $do_jlon->insertAfter (&s ("YLSTACK%U = stack_u (YSTACK, JBLK-$JBLKMIN+1, $KGPBLKS)"), $do_jlon->firstChild);
      $do_jlon->insertAfter (&t ("\n" . (' ' x $indent)), $do_jlon->firstChild);
      $do_jlon->insertAfter (&s ("YLSTACK%L = stack_l (YSTACK, JBLK-$JBLKMIN+1, $KGPBLKS)"), $do_jlon->firstChild);
      $do_jlon->insertAfter (&t ("\n" . (' ' x $indent)), $do_jlon->firstChild);
    }


}

sub addStack
{
  my ($d, %opts) = @_;

  my @KLON = @{ $opts{KLON} || [qw (KLON YDCPG_OPTS%KLON)] };

  my @pointer = @{ $opts{pointer} || [] };

  my $skip = $opts{skip};
  my $local = exists $opts{local} ? $opts{local} : 1;

  my @call = &F ('.//call-stmt[string(procedure-designator)!="ABOR1" and string(procedure-designator)!="REDUCE"]', $d);

  my %contained = map { ($_, 1) } &F ('.//subroutine-N[count(ancestor::program-unit)>1]', $d, 1);

  my $YLSTACK = $local ? 'YLSTACK' : 'YDSTACK';

  for my $call (@call)
    {
      my ($proc) = &F ('./procedure-designator', $call, 1);
      next if ($proc eq 'DR_HOOK');
      next if ($contained{$proc});
      next if ($proc =~ m/%/o);
      if ($skip)
        {
          next if ($skip->($proc, $call));
        }
      my ($argspec) = &F ('./arg-spec', $call);
      $argspec->appendChild (&t (', '));

      my $arg = &n ('<arg/>');

      $arg->appendChild (&n ('<arg-N n="YDSTACK"><k>YDSTACK</k></arg-N>'));
      $arg->appendChild (&t ('='));
      $arg->appendChild (&e ($YLSTACK));

      $argspec->appendChild ($arg);
    }

  my ($dummy_arg_lt) = &F ('.//subroutine-stmt/dummy-arg-LT', $d);

  my @args = &F ('./arg-N', $dummy_arg_lt, 1);

  my $last = $args[-1];

  $dummy_arg_lt->appendChild (&t (', '));
  $dummy_arg_lt->appendChild (&n ("<arg-N><N><n>YDSTACK</n></N></arg-N>"));

  my ($use) = &F ('.//use-stmt[last()]', $d);
  $use->parentNode->insertAfter (&n ("<include>#include &quot;<filename>stack.h</filename>&quot;</include>"), $use);
  $use->parentNode->insertAfter (&t ("\n"), $use);
  $use->parentNode->insertAfter (&s ("USE STACK_MOD"), $use);
  $use->parentNode->insertAfter (&t ("\n"), $use);
  $use->parentNode->insertAfter (&s ("USE ABOR1_ACC_MOD"), $use);
  $use->parentNode->insertAfter (&t ("\n"), $use);

  my ($decl) = &F ('.//T-decl-stmt[.//EN-N[string(.)="?"]]', $last, $d);

  if ($local)
    {
      $decl->parentNode->insertAfter (&s ("#include \"stack.head.h\""), $decl);
      $decl->parentNode->insertAfter (&t ("\n"), $decl);
      $decl->parentNode->insertAfter (&s ("TYPE(STACK) :: YLSTACK"), $decl);
      $decl->parentNode->insertAfter (&t ("\n"), $decl);
    }

  $decl->parentNode->insertAfter (&s ("TYPE(STACK) :: YDSTACK"), $decl);
  $decl->parentNode->insertAfter (&t ("\n"), $decl);

  
  my $noexec = &Scope::getNoExec ($d);

  my $C = &n ("<C/>");

  $noexec->parentNode->insertAfter (&t ("\n"), $noexec);
  $noexec->parentNode->insertAfter ($C, $noexec);

  if ($local)
    {
      $C->parentNode->insertBefore (&t ("\n"), $C);
      $C->parentNode->insertBefore (&t ("\n"), $C);
      $C->parentNode->insertBefore (&s ("YLSTACK = YDSTACK"), $C);
      $C->parentNode->insertBefore (&t ("\n"), $C);
      $C->parentNode->insertBefore (&t ("\n"), $C);
    }


  my %args = map { ($_, 1) } @args;

  for my $KLON (@KLON)
    {
      my @en_decl = &F ('.//T-decl-stmt'
                      . '//EN-decl[./array-spec/shape-spec-LT/shape-spec[string(./upper-bound)="?"]]', 
                      $KLON, $d);
      

      for my $en_decl (@en_decl)
        {
          my ($n) = &F ('./EN-N', $en_decl, 1);

          next if ($args{$n});

          my $stmt = &Fxtran::stmt ($en_decl);

          my ($t) = &F ('./_T-spec_',   $stmt);     &Fxtran::expand ($t); $t = $t->textContent;
          my ($s) = &F ('./array-spec', $en_decl);  &Fxtran::expand ($s); 

          my (@lb, @ub, @sz);

          my @ss = &F ('./shape-spec-LT/shape-spec', $s);

          my $nd = scalar (@ss);
      
          for my $ss (@ss)
            {
              my ($lb) = &F ('./lower-bound/ANY-E', $ss, 1); $lb = 1 unless (defined ($lb)); 
              my ($ub) = &F ('./upper-bound/ANY-E', $ss, 1); 
              my $sz = "$ub-($lb)+1";
              $sz = $ub if ($lb eq '1');
              $sz = "$ub+1" if ($lb eq '0');
              push @lb, $lb;
              push @ub, $ub;
              push @sz, $sz;
            }

          if ($local)
            {
              my $S = join (', ', (':') x $nd);
              $stmt->parentNode->insertBefore (my $temp = &t ("temp ($t, $n, ($S))"), $stmt);
      
              if (&Fxtran::removeListElement ($en_decl))
                {
                  $stmt->unbindNode ();
                }
              else
                {
                  $temp->parentNode->insertAfter (&t ("\n"), $temp);
                }
      
              if (! grep { $n eq $_ } @pointer)
                {
                  if ($opts{stack84})
                    {
                      my $SZ = join ('*', map { $sz[$_] =~ m/^\w+$/o ? $sz[$_] : "($sz[$_])" } (0 .. $nd-1));
                      my $SH = join (',', map { "$lb[$_]:$ub[$_]" } (0 .. $nd-1));

                      my $LB = join (',', @lb);
                      my $UB = join (',', @ub);

                      my $alloc;

                      $alloc = &s ("alloc ($n, (/$LB/), (/$UB/))");

                      $C->parentNode->insertBefore ($alloc, $C);
                      $C->parentNode->insertBefore (&t ("\n"), $C);
                    }
                  else
                    {
                      $C->parentNode->insertBefore (&t ("alloc ($n)\n"), $C);
                    }

                }
            }
          else
            {
              die "No local stack, but KLON arrays were found";
            }

        }

    }

  $C->unbindNode ();


  my ($end) = &F ('./object/file/program-unit/end-subroutine-stmt', $d);

  for my $stmt (&n ("<contains-stmt>CONTAINS</contains-stmt>"), &t ("\n"), &s ("#include \"stack.tail.h\""), &t ("\n"))
    {
      $end->parentNode->insertBefore ($stmt, $end);
    }


}

1;
