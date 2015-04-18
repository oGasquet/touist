==== GPW 2.x solver ==== 

Overall:
GPW is pseudo-boolean solver of linear problems.  

Linear constraint y1-3*y2 = 0 is described as
  1 y1 -3 y2 = 0

In addition to oridinal constraints interpreted conjunction.  This
solver of versions later than or equal 2.01 has a facility of
difinition, which enables us to write complex formulas like CNFs.  For
example, for linear constraints c1, c2, ..., to denote (c1 or c2) and
(c3 or c4):
  d x1 <=> c1 ;
  d x2 <=> c2 ;
  1 x1 1 x2 >= 1 ;
  d x3 <=> c3 ;
  d x4 <=> c4 ;
  1 x3 1 x4 >= 1 ;

Negated boolean variable is also accepted, like
  1 ~x1 2 x2 3 ~x3 = 3;

===
GPW 2.x is developped based on minisatp-1.0: 
  http://minisat.se/MiniSat+.html
We thank Niklas Eén and Niklas Sörensson.

GPW 1.x is an originally implemented solver for pseudo-Boolean problems
consist of linear arithmetic constraints.  For basic design of this solver,
see 
  Olivier Bailleux, Yacine Boufkhad, Olivier Roussel: 
  New Encodings of Pseudo-Boolean Constraints into CNF.
  SAT 2009: 181-194
Version 1.00 is written by Chang CHAI. All the other versions are
developped by Masahiko Sakai.
----------------------------------------------------------------------
Usage: Try 
     gpw --help

----------------------------------------------------------------------

Known BUG:
- From Version 2.00, combination of -S and -cnf option may produces
  CNFs having wrong model.
- The option -model-check introduced in Version 2.05 has a bug.

History:

Version 2.09 Sep 25, 2013.
  - Fixed the bug that the option -bdd-m may result unsatisiable 
    for some satisfiable problems.

Version 2.08 Sep 21, 2013.
  - Fixed the bug that -bdd-i may cause 'segmentation fault'.

Version 2.07 Sep 19, 2013.
  - Added a option -bdd-i:
     -bdd-i: Creating BDDs with interval.
     -bdd-r: Creating BDDs in reverse (co-efficient increasing) order.

Version 2.06 Sep 15, 2013.
  - Added a option -bdd-b:
     -bdd-b: Clausify BDDs after binary-decomposition of coefficients.
  - Fixed serious bug on the option -bdd-m.

Version 2.05 Sep 13, 2013.
  - Added options -m, -bdd-m, -model-check:
     -bdd-m: clausify BDDs using monotonicity. (-m will become true)
     -m    : always keeps constraints with monotonic in internal data.
     -mc, -model-check: do model checking if the results are satisfiable.

Version 2.04-2 Sep 5, 2013.
  - Fixed a bug that -S option option fails to produce variable 
    map in cnf files.

Version 2.04-1 Sep 4, 2013.
  - Fixed a bug that may produce incorrect CNFs with -cnf option.

Version 2.04 June 9, 2013.
  - Five kinds of coding in GPW are implemented:
     -gpw-pos: convert constraint (1)Sigma_term >= b,
     -gpw-neg: convert constraint (2)Sigma_term < b,
     -gpw-lo:  choose (1) or (2) having smaller b,
     -gpw-hi:  choose (1) or (2) having larger b,
     -gpw-both:convert both (1) and (2).

Version 2.03 June 5, 2013.
  - Fixed a serious bug in 2.02 on global watch dog implementation.
  - Fixed the bug that correspondence output in cnf-file between
      variables in the cnf-file and described variables in the input file.
  - In Global watch dog, added choise between >= type and < type.

Version 2.02 May 28, 2013.
  - Global watch dog, like gpw 1.0x, installed for sorter conversion.
    To switch off this function, use -wg or -without-gpw option.
  - Negation of boolean variable, like ~x0.

Version 2.01 May 27, 2013.
  - SMT extension.  Definitions like the following are allowed:
      d x0 <=> c1 x1 c2 x2 ... <= b
    which means that x0 iff the followint linear constraint.
    This extension enable us to write complex descritpion.

Version 2.00 May 23, 2013.
  - Stronger OR detection.
  - Fit to FreeBSD environment.

Version 1.05 may 21, 2013.
  - Stronger OR detection.
  - Small reduction of new variables.
  - AND detection.
  - -e option for producing with es1 clauses (LessThan2 detection)

Version 1.04  May 17, 2013.
  - Improved input routine.
  - Improved memory size estimation in malloc.

Version 1.03  May 16, 2013.
  - Acceptation of old style Pseudo-Boolean format like
       1*x1 -2*x3 >= 1.
  - Code for operator <, <=, > in addition to >=
  - Improvement by OR detection.  An opthin -O force to skip this function.
  - Fixed a segmantation fault problem.
  - Code for ignoring min function.

Version 1.02  May 15, 2013.
  - Fixed an memory allocation bug on amd64 machine.
  - Fixed a bug on treatments of fresh boolean variables.
  - Modification by Masahiko SAKAI after this release.

Version 1.01  March 21, 2013.
  - Firstly released.
