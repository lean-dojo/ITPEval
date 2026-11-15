;; Statement-only formalization of PutnamBench corpus artifact putnam_1996_a3:
;; the universal claim that every assignment of subsets of six courses to
;; twenty students has five students and two courses that all five either
;; take together or omit together is false. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; A student's chosen course set is its 6-bit characteristic number. A full
;; choice function is the 20-digit base-64 number whose digit at position S is
;; student S's course set. These are bijections with Set (Fin 6) and with all
;; functions Fin 20 -> Set (Fin 6), respectively.

(defun putnam-1996-a3-choice-set
    (choices-code student)
  (mod
   (floor choices-code (expt 64 student))
   64))

(defun putnam-1996-a3-member-p
    (set-code element)
  (equal
   (mod
    (floor set-code (expt 2 element))
    2)
   1))

(defun putnam-1996-a3-cardinality
    (set-code width)
  (declare (xargs :measure (nfix width)))
  (if (zp width)
      0
    (+
     (mod set-code 2)
     (putnam-1996-a3-cardinality
      (floor set-code 2)
      (- width 1)))))

;; MODE is true for "chosen" and false for "not chosen." This checks every
;; selected course for one student.
(defun putnam-1996-a3-student-agrees-p
    (choices-code student course-set course-count mode)
  (declare (xargs :measure (nfix course-count)))
  (if (zp course-count)
      t
    (let* ((course (- course-count 1))
           (course-selected
            (putnam-1996-a3-member-p course-set course))
           (course-chosen
            (putnam-1996-a3-member-p
             (putnam-1996-a3-choice-set
              choices-code student)
             course)))
      (and
       (or
        (not course-selected)
        (equal course-chosen mode))
       (putnam-1996-a3-student-agrees-p
        choices-code
        student
        course-set
        course
        mode)))))

;; This checks that every selected student agrees with MODE on both selected
;; courses.
(defun putnam-1996-a3-students-agree-p
    (choices-code student-set course-set student-count mode)
  (declare (xargs :measure (nfix student-count)))
  (if (zp student-count)
      t
    (let ((student (- student-count 1)))
      (and
       (or
        (not
         (putnam-1996-a3-member-p
          student-set student))
        (putnam-1996-a3-student-agrees-p
         choices-code student course-set 6 mode))
       (putnam-1996-a3-students-agree-p
        choices-code
        student-set
        course-set
        student
        mode)))))

;; Search all subsets of the six courses for a two-course witness.
(defun putnam-1996-a3-course-witness-p
    (choices-code student-set course-candidates)
  (declare (xargs :measure (nfix course-candidates)))
  (if (zp course-candidates)
      nil
    (let ((course-set (- course-candidates 1)))
      (or
       (and
        (equal
         (putnam-1996-a3-cardinality course-set 6)
         2)
        (or
         (putnam-1996-a3-students-agree-p
          choices-code student-set course-set 20 t)
         (putnam-1996-a3-students-agree-p
          choices-code student-set course-set 20 nil)))
       (putnam-1996-a3-course-witness-p
        choices-code student-set course-set)))))

;; Search all subsets of the twenty students for a five-student witness.
(defun putnam-1996-a3-student-witness-p
    (choices-code student-candidates)
  (declare (xargs :measure (nfix student-candidates)))
  (if (zp student-candidates)
      nil
    (let ((student-set (- student-candidates 1)))
      (or
       (and
        (equal
         (putnam-1996-a3-cardinality student-set 20)
         5)
        (putnam-1996-a3-course-witness-p
         choices-code student-set (expt 2 6)))
       (putnam-1996-a3-student-witness-p
        choices-code student-set)))))

(defun putnam-1996-a3-choice-property-p
    (choices-code)
  (putnam-1996-a3-student-witness-p
   choices-code (expt 2 20)))

;; This is the source's universal quantifier over the complete finite function
;; space, not a sample or bounded approximation.
(defun putnam-1996-a3-all-choice-functions-p
    (choice-function-candidates)
  (declare (xargs :measure (nfix choice-function-candidates)))
  (if (zp choice-function-candidates)
      t
    (let ((choices-code (- choice-function-candidates 1)))
      (and
       (putnam-1996-a3-choice-property-p choices-code)
       (putnam-1996-a3-all-choice-functions-p
        choices-code)))))

;; The designated solution is False, so the source biconditional is exactly
;; the negation of the universal claim above.
(defun putnambench-putnam-1996-a3-statement ()
  (not
   (putnam-1996-a3-all-choice-functions-p
    (expt 64 20))))

(value-triple :itpeval-statement-checked)
:q
