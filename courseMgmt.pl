% --------------- Variables de estado ---------------
variables([EStudents, AProfessors]).

% -------------- Definiciones de tipos --------------
def_type(ss,set(student)).
def_type(pp, set(professor)).
def_type(es,rel(course,ss)).
def_type(ap,rel(course,pp)).

% -------------- Invariantes de estado --------------
invariant(courseMgmtInv).

dec_p_type(courseMgmtInv(es, ap)).
courseMgmtInv(EStudents, AProfessors) :- let([DomE, DomA], dec(DomE, set(course)) & dec(DomA, set(course)) & dom(EStudents, DomE) & dom(AProfessors, DomA), subset(DomE, DomA)).

dec_p_type(n_courseMgmtInv(es, ap)).
n_courseMgmtInv(EStudents, AProfessors) :- neg(let([DomE, DomA], dec(DomE, set(course)) & dec(DomA, set(course)) & dom(EStudents, DomE) & dom(AProfessors, DomA), subset(DomE, DomA))).

invariant(eStudentsFunInv).

dec_p_type(eStudentsFunInv(es)).
eStudentsFunInv(EStudents) :- pfun(EStudents).

dec_p_type(n_eStudentsFunInv(es)).
n_eStudentsFunInv(EStudents) :- neg(pfun(EStudents)).

invariant(aProfessorsFunInv).

dec_p_type(aProfessorsFunInv(ap)).
aProfessorsFunInv(AProfessors) :- pfun(AProfessors).

dec_p_type(n_aProfessorsFunInv(ap)).
n_aProfessorsFunInv(AProfessors) :- neg(pfun(AProfessors)).

% ------------------ Estado incial ------------------
initial(courseMgmtInit).
dec_p_type(courseMgmtInit(es,ap)).
courseMgmtInit(EStudents, AProfessors) :- EStudents = {} & AProfessors = {}.

% ------------------- Operaciones -------------------

% ---- EnrollStudent ----

% EnrollStudentOldCourse
dec_p_type(enrollStudentOldCourseOk(es, ap, student, course, es)).
enrollStudentOldCourseOk(EStudents, AProfessors, Student, Course, EStudents_) :-
  dom(AProfessors, DomA) &
  dec(DomA, set(course)) &
  Course in DomA &
  dom(EStudents, DomE) &
  dec(DomE, set(course)) &
  Course in DomE &
  applyTo(EStudents, Course, Enrolled) &
  dec(Enrolled, ss) &
  Student nin Enrolled &
  oplus(EStudents, {[Course, {Student / Enrolled}]}, EStudents_).
  
% EnrollStudentNewCourse
dec_p_type(enrollStudentNewCourseOk(es, ap, student, course, es)).
enrollStudentNewCourseOk(EStudents, AProfessors, Student, Course, EStudents_) :-
  dom(AProfessors, DomA) &
  dec(DomA, set(course)) &
  Course in DomA &
  dom(EStudents, DomE) &
  dec(DomE, set(course)) &
  Course nin DomE &
  EStudents_ = {[Course, {Student}] / EStudents}.
  
% StudentAlreadyInCourse
dec_p_type(studentAlreadyInCourse(es, ap, student, course, es)).
studentAlreadyInCourse(EStudents, AProfessors, Student, Course, EStudents_) :-
  dom(AProfessors, DomA) &
  dec(DomA, set(course)) &
  Course in DomA &
  dom(EStudents, DomE) &
  dec(DomE, set(course)) &
  Course in DomE &
  applyTo(EStudents, Course, Enrolled) &
  dec(Enrolled, ss) &
  Student in Enrolled &
  EStudents_ = EStudents.

% CourseNotReady
dec_p_type(courseNotReady(es, ap, course, es)).
courseNotReady(EStudents, AProfessors, Course, EStudents_) :-
  dom(AProfessors, DomA) &
  dec(DomA, set(course)) &
  Course nin DomA &
  EStudents_ = EStudents.

% EnrollStudent
operation(enrollStudent).
dec_p_type(enrollStudent(es, ap, student, course, es)).
enrollStudent(EStudents, AProfessors, Student, Course, EStudents_) :-
  enrollStudentOldCourseOk(EStudents, AProfessors, Student, Course, EStudents_) or
  enrollStudentNewCourseOk(EStudents, AProfessors, Student, Course, EStudents_) or
  courseNotReady(EStudents, AProfessors, Course, EStudents_) or
  studentAlreadyInCourse(EStudents, AProfessors, Student, Course, EStudents_).

% ---- AssignProfessors ----

% AssignProfessorsOk
dec_p_type(assignProfessorOk(ap, pp, course, ap)).
assignProfessorOk(AProfessors, Professors, Course, AProfessors_) :-
  dom(AProfessors, DomA) &
  dec(DomA, set(course)) &
  Course nin DomA &
  un(AProfessors, {[Course, Professors]}, AProfessors_).

% CourseAlreadyAssigned
dec_p_type(courseAlreadyAssigned(ap, course, ap)).
courseAlreadyAssigned(AProfessors, Course, AProfessors_) :-
  dom(AProfessors, DomA) &
  dec(DomA, set(course)) &
  Course in DomA &
  AProfessors_ = AProfessors.
  

% AssignProfessors
operation(assignProfessors).
dec_p_type(assignProfessors(ap, pp, course, ap)).
assignProfessors(AProfessors, Professor, Course, AProfessors_) :-
  assignProfessorOk(AProfessors, Professor, Course, AProfessors_) or
  courseAlreadyAssigned(AProfessors, Course, AProfessors_).

% ---- ShowCourseInfo ----

% ShowCourseInfoWithStudentsOk
dec_p_type(showCourseInfoWithStudents(es, ap, course, ss, pp)).
showCourseInfoWithStudents(EStudents, AProfessors, Course, Students, Professors) :-
  dom(AProfessors, DomA) &
  dec(DomA, set(course)) &
  Course in DomA &
  dom(EStudents, DomE) &
  dec(DomE, set(course)) &
  Course in DomE &
  applyTo(EStudents, Course, Students) &
  applyTo(AProfessors, Course, Professors).

% ShowCourseInfoWithoutStudentsOk
dec_p_type(showCourseInfoWithoutStudents(es, ap, course, ss, pp)).
showCourseInfoWithoutStudents(EStudents, AProfessors, Course, Students, Professors) :-
  dom(AProfessors, DomA) &
  dec(DomA, set(course)) &
  Course in DomA &
  dom(EStudents, DomE) &
  dec(DomE, set(course)) &
  Course nin DomE &
  Students = {} &
  applyTo(AProfessors, Course, Professors).
  
% NoInfoToShow
dec_p_type(noInfoToShow(ap,course, ss, pp)).
noInfoToShow(AProfessors, Course, Students, Professors) :-
  dom(AProfessors, DomA) &
  dec(DomA, set(course)) &
  Course nin DomA &
  Students = {} &
  Professors = {}.

% ShowCourseInfo
operation(showCourseInfo).
dec_p_type(showCourseInfo(es, ap, course, ss, pp)).
showCourseInfo(EStudents, AProfessors, Course, Students, Professors) :-
  showCourseInfoWithStudents(EStudents, AProfessors, Course, Students, Professors) or
  showCourseInfoWithoutStudents(EStudents, AProfessors, Course, Students, Professors) or
  noInfoToShow(AProfessors, Course, Students, Professors).
  
