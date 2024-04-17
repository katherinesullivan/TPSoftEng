% Verification conditions for courseMgmt.pl

% Run check_vcs_courseMgmt to see if the program verifies all the VCs

:- notype_check.

:- consult('courseMgmt.pl').

:- prolog_call((
    retractall(all_unsat_vc(_,_,_,_,_,_)),
    retractall(dinvariant(_,_,_)),
    retractall(daxiom(_,_,_)),
    (exists_file('courseMgmt-all.pl') ->
       open('courseMgmt-all.pl',read,StreamVC)
    ;
       print_notfile('courseMgmt-all.pl')
    ),
    style_check(-singleton),
    setlog:consult_vc(StreamVC),
    style_check(+singleton),
    close(StreamVC))).

% Change this number for a different timeout (ms)
def_to(60000).

:- prolog_call(nb_setval(vc_num,0)).
:- prolog_call(nb_setval(vc_ok,0)).
:- prolog_call(nb_setval(vc_err,0)).
:- prolog_call(nb_setval(vc_to,0)).
:- prolog_call(nb_setval(vc_time,0)).

:- prolog_call(dynamic(unsat_sol/5)).
:- prolog_call(dynamic(vc_proved/1)).

courseMgmtInit_sat_courseMgmtInv :-
  courseMgmtInit(EStudents,AProfessors) &
  courseMgmtInv(EStudents,AProfessors).

courseMgmtInit_sat_eStudentsFunInv :-
  courseMgmtInit(EStudents,AProfessors) &
  eStudentsFunInv(EStudents).

courseMgmtInit_sat_aProfessorsFunInv :-
  courseMgmtInit(EStudents,AProfessors) &
  aProfessorsFunInv(AProfessors).

enrollStudent_is_sat :-
  enrollStudent(EStudents,AProfessors,Student,Course,EStudents_) & 
  EStudents neq EStudents_.

enrollStudent_pi_courseMgmtInv(EStudents,AProfessors,EStudents,AProfessors,Student,Course,EStudents_) :-
  % here conjoin other ax/inv as hypothesis if necessary
  neg(
    courseMgmtInv(EStudents,AProfessors) &
    enrollStudent(EStudents,AProfessors,Student,Course,EStudents_) implies
    courseMgmtInv(EStudents_,AProfessors)
  ).

enrollStudent_pi_eStudentsFunInv(EStudents,EStudents,AProfessors,Student,Course,EStudents_) :-
  % here conjoin other ax/inv as hypothesis if necessary
  neg(
    eStudentsFunInv(EStudents) &
    enrollStudent(EStudents,AProfessors,Student,Course,EStudents_) implies
    eStudentsFunInv(EStudents_)
  ).

enrollStudent_pi_aProfessorsFunInv(AProfessors,EStudents,AProfessors,Student,Course,EStudents_):-
  % enrollStudent doesn't change aProfessorsFunInv variables
  neg(true).

assignProfessors_is_sat :-
  assignProfessors(AProfessors,Professor,Course,AProfessors_) & 
  AProfessors neq AProfessors_.

assignProfessors_pi_courseMgmtInv(EStudents,AProfessors,AProfessors,Professor,Course,AProfessors_) :-
  % here conjoin other ax/inv as hypothesis if necessary
  neg(
    courseMgmtInv(EStudents,AProfessors) &
    assignProfessors(AProfessors,Professor,Course,AProfessors_) implies
    courseMgmtInv(EStudents,AProfessors_)
  ).

assignProfessors_pi_eStudentsFunInv(EStudents,AProfessors,Professor,Course,AProfessors_):-
  % assignProfessors doesn't change eStudentsFunInv variables
  neg(true).

assignProfessors_pi_aProfessorsFunInv(AProfessors,AProfessors,Professor,Course,AProfessors_) :-
  % here conjoin other ax/inv as hypothesis if necessary
  neg(
    aProfessorsFunInv(AProfessors) &
    assignProfessors(AProfessors,Professor,Course,AProfessors_) implies
    aProfessorsFunInv(AProfessors_)
  ).

showCourseInfo_is_sat :-
  showCourseInfo(EStudents,AProfessors,Course,Students,Professors).

showCourseInfo_pi_courseMgmtInv(EStudents,AProfessors,EStudents,AProfessors,Course,Students,Professors):-
  % showCourseInfo doesn't change courseMgmtInv variables
  neg(true).

showCourseInfo_pi_eStudentsFunInv(EStudents,EStudents,AProfessors,Course,Students,Professors):-
  % showCourseInfo doesn't change eStudentsFunInv variables
  neg(true).

showCourseInfo_pi_aProfessorsFunInv(AProfessors,EStudents,AProfessors,Course,Students,Professors):-
  % showCourseInfo doesn't change aProfessorsFunInv variables
  neg(true).

update_time(Tf,Ti) :-
  prolog_call(
    (nb_getval(vc_time,VCT),
     VCT_ is VCT + Tf - Ti,
     nb_setval(vc_time,VCT_)
    )
  ).

update_count(C) :-
  prolog_call(
    (nb_getval(C,VCN),
     VCN_ is VCN + 1,
     nb_setval(C,VCN_)
    )
  ).

check_sat_vc(VCID) :-
  prolog_call((setlog:vc_proved(VCID) -> R = proved ; R = unproved)) &
  (R == unproved &
   write('\nChecking ') & write(VCID) & write(' ... ') &
   update_count(vc_num) &
   ((prolog_call(setlog(VCID)) &
    update_count(vc_ok) &
    prolog_call(assertz(vc_proved(VCID))) &
    write_ok)!
    or
    update_count(vc_err) &
    write_err
   )
   or
   R == proved
  ).

check_unsat_vc(VCID) :-
  def_to(TO) &
  prolog_call(
    (VCID =.. [H | _],
     (\+setlog:vc_proved(H) ->
        setlog:all_unsat_vc(H,T,ID,VC,Op,VN),
        write('\nChecking '), write(H), write(' ... '), flush_output,
        setlog(update_count(vc_num)),
        get_time(Ti),
        rsetlog(VC,TO,Cons,Res,[nopfcheck]),
        get_time(Tf)
     ;
        Res = proved
     )
    )
  ) &
  ((Res = failure)! &
    update_count(vc_ok) &
    update_time(Tf,Ti) &
    prolog_call((retractall(setlog:unsat_sol(_,H,_,_,_)),
                 assertz(vc_proved(H)))) &
    write_ok
  or
   (Res = timeout)! &
    update_count(vc_to) &
    write_to
  or
    (Res = proved)!
  or
    update_count(vc_err) &
    % saves the solution to be used by findh
    prolog_call((retractall(setlog:unsat_sol(_,H,_,_,_)),
                 assertz(unsat_sol(T,H,ID,Cons,VN)))) &
    write_err
  ).

write_ok :-
  prolog_call(ansi_format([bold,fg(green)],'OK',[])).

write_to :-
  prolog_call(ansi_format([bold,fg(255,255,50)],'TIMEOUT',[])).

write_err :-
  prolog_call(ansi_format([bold,fg(red)],'ERROR',[])).

check_vcs_courseMgmt :- prolog_call(setlog(check_aux!)).

check_aux :-
  prolog_call(
    (retractall(unsat_sol(_,_,_,_,_)),
     nb_setval(vc_num,0),
     nb_setval(vc_time,0),
     nb_setval(vc_ok,0),
     nb_setval(vc_err,0),
     nb_setval(vc_to,0)
    )
  ) &
  check_sat_vc(courseMgmtInit_sat_courseMgmtInv) &
  check_sat_vc(courseMgmtInit_sat_eStudentsFunInv) &
  check_sat_vc(courseMgmtInit_sat_aProfessorsFunInv) &
  check_sat_vc(enrollStudent_is_sat) &
  check_sat_vc(assignProfessors_is_sat) &
  check_sat_vc(showCourseInfo_is_sat) &
  check_unsat_vc(enrollStudent_pi_courseMgmtInv(EStudents,AProfessors,EStudents,AProfessors,Student,Course,EStudents_)) &
  check_unsat_vc(enrollStudent_pi_eStudentsFunInv(EStudents,EStudents,AProfessors,Student,Course,EStudents_)) &
  check_unsat_vc(enrollStudent_pi_aProfessorsFunInv(AProfessors,EStudents,AProfessors,Student,Course,EStudents_)) &
  check_unsat_vc(assignProfessors_pi_courseMgmtInv(EStudents,AProfessors,AProfessors,Professor,Course,AProfessors_)) &
  check_unsat_vc(assignProfessors_pi_eStudentsFunInv(EStudents,AProfessors,Professor,Course,AProfessors_)) &
  check_unsat_vc(assignProfessors_pi_aProfessorsFunInv(AProfessors,AProfessors,Professor,Course,AProfessors_)) &
  check_unsat_vc(showCourseInfo_pi_courseMgmtInv(EStudents,AProfessors,EStudents,AProfessors,Course,Students,Professors)) &
  check_unsat_vc(showCourseInfo_pi_eStudentsFunInv(EStudents,EStudents,AProfessors,Course,Students,Professors)) &
  check_unsat_vc(showCourseInfo_pi_aProfessorsFunInv(AProfessors,EStudents,AProfessors,Course,Students,Professors)) &
  prolog_call(
    (nb_getval(vc_num,VCN),
     nb_getval(vc_time,VCT),
     nb_getval(vc_ok,VCOK),
     nb_getval(vc_err,VCE),
     nb_getval(vc_to,VCTO)
    )
  ) &
  nl & nl &
  write("Total VCs: ") & write(VCN) &
  write(" (discharged: ") & write(VCOK) &
  write(", failed: ") & write(VCE) &
  write(", timeout: ") & write(VCTO) & write(")") & nl &
  write("Execution time (discharged): ") & write(VCT) & write(" s").

:- nl & prolog_call(ansi_format([bold,fg(green)],'Type checking has been deactivated.',[])) & nl & nl.

:- nl & prolog_call(ansi_format([bold,fg(green)],'Call check_vcs_courseMgmt to run the verification conditions.',[])) & nl & nl.

