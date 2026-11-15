;; Statement-only formalization of PutnamBench corpus artifact putnam_2000_b5:
;; a finite positive-integer set sequence evolving by symmetric difference
;; with its unit shift has arbitrarily late terms equal to the union of its
;; initial set and an index-translate of that set. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; SEQUENCE is an ACL2 function object whose value at (n,a), for natural n
;; and integer a, is membership of a in S_n. Its otherwise unused value at
;; (nil,nil) carries a natural upper bound for S_0. This decorated function
;; representation is bidirectionally equivalent to a sequence of finite sets:
;; forget the out-of-domain value in one direction, and store any bound for
;; the finite positive set S_0 in the other. APPLY$ and FN-EQUAL retain the
;; arbitrary source membership function and quantify extensionally over its
;; typed arguments; no finite table replaces the infinite sequence.

(defun putnam-2000-b5-quoted (object)
  (list 'quote object))

(defun putnam-2000-b5-term-list (terms)
  (if (consp terms)
      (list 'cons
            (car terms)
            (putnam-2000-b5-term-list (cdr terms)))
    nil))

(defun putnam-2000-b5-apply-term (function arguments)
  (list 'apply$
        (putnam-2000-b5-quoted function)
        (putnam-2000-b5-term-list arguments)))

(defun putnam-2000-b5-and-terms (terms)
  (if (consp terms)
      (list 'if
            (car terms)
            (putnam-2000-b5-and-terms (cdr terms))
            (putnam-2000-b5-quoted nil))
    (putnam-2000-b5-quoted t)))

(defun putnam-2000-b5-implies-term (hypothesis conclusion)
  (list 'if
        hypothesis
        conclusion
        (putnam-2000-b5-quoted t)))

(defun putnam-2000-b5-less-equal-term (left right)
  (list 'if
        (list '< right left)
        (putnam-2000-b5-quoted nil)
        (putnam-2000-b5-quoted t)))

(defun putnam-2000-b5-true-function (formals)
  (list 'lambda
        formals
        (putnam-2000-b5-quoted t)))

(defun putnam-2000-b5-member-term
    (sequence index element)
  (list 'if
        (putnam-2000-b5-apply-term
         sequence (list index element))
        (putnam-2000-b5-quoted t)
        (putnam-2000-b5-quoted nil)))

;; This exact function object is the canonical executable representation of
;; the all-empty sequence. Recognizing it only normalizes a concrete model;
;; every other sequence is checked by the full extensional matrices below.

(defun putnam-2000-b5-empty-sequence-p (sequence)
  (equal sequence
         '(lambda (n a) 'nil)))

;; Because every source member is a positive integer, S_0 is finite exactly
;; when it has a natural upper bound. The recurrence propagates finite support,
;; so checking the represented bound for S_0 is equivalent to the source
;; assumption that every S_n is finite.

(defun putnam-2000-b5-support-bound (sequence)
  (nfix (apply$ sequence (list nil nil))))

(defun putnam-2000-b5-initial-bound-function
    (sequence bound)
  (let ((member
         (putnam-2000-b5-member-term
          sequence
          (putnam-2000-b5-quoted 0)
          'a)))
    (list
     'lambda
     '(a)
     (putnam-2000-b5-implies-term
      (putnam-2000-b5-and-terms
       (list
        (list 'integerp 'a)
        member))
      (putnam-2000-b5-less-equal-term
       'a bound)))))

(defun putnam-2000-b5-finite-initial-p (sequence)
  (if (putnam-2000-b5-empty-sequence-p sequence)
      t
    (let* ((bound
            (putnam-2000-b5-support-bound sequence))
           (bound-function
            (putnam-2000-b5-initial-bound-function
             sequence (putnam-2000-b5-quoted bound)))
           (true-function
            (putnam-2000-b5-true-function '(a))))
      (and
       (tamep-functionp bound-function)
       (tamep-functionp true-function)
       (fn-equal bound-function true-function)))))

;; These two FN-EQUAL matrices are the source assumptions
;;
;;   all members of every S_n are positive integers, and
;;   a in S_(n+1) iff exactly one of a-1 and a belongs to S_n.

(defun putnam-2000-b5-positive-function (sequence)
  (let ((member
         (putnam-2000-b5-member-term
          sequence 'n 'a)))
    (list
     'lambda
     '(n a)
     (putnam-2000-b5-implies-term
      (putnam-2000-b5-and-terms
       (list
        (list 'natp 'n)
        (list 'integerp 'a)
        member))
      (list '<
            (putnam-2000-b5-quoted 0)
            'a)))))

(defun putnam-2000-b5-positive-p (sequence)
  (if (putnam-2000-b5-empty-sequence-p sequence)
      t
    (let ((positive-function
           (putnam-2000-b5-positive-function sequence))
          (true-function
           (putnam-2000-b5-true-function '(n a))))
      (and
       (tamep-functionp positive-function)
       (tamep-functionp true-function)
       (fn-equal positive-function true-function)))))

(defun putnam-2000-b5-recurrence-function (sequence)
  (let* ((next-index
          (list
           'binary-+
           'n
           (putnam-2000-b5-quoted 1)))
         (previous-element
          (list
           'binary-+
           'a
           (putnam-2000-b5-quoted -1)))
         (next-member
          (putnam-2000-b5-member-term
           sequence next-index 'a))
         (previous-member
          (putnam-2000-b5-member-term
           sequence 'n previous-element))
         (current-member
          (putnam-2000-b5-member-term
           sequence 'n 'a))
         (exclusive-member
          (list
           'if
           (list 'equal previous-member current-member)
           (putnam-2000-b5-quoted nil)
           (putnam-2000-b5-quoted t))))
    (list
     'lambda
     '(n a)
     (putnam-2000-b5-implies-term
      (putnam-2000-b5-and-terms
       (list
        (list 'natp 'n)
        (list 'integerp 'a)))
      (list 'equal next-member exclusive-member)))))

(defun putnam-2000-b5-recurrence-p (sequence)
  (if (putnam-2000-b5-empty-sequence-p sequence)
      t
    (let ((recurrence-function
           (putnam-2000-b5-recurrence-function sequence))
          (true-function
           (putnam-2000-b5-true-function '(n a))))
      (and
       (tamep-functionp recurrence-function)
       (tamep-functionp true-function)
       (fn-equal recurrence-function true-function)))))

;; If B bounds S_0, the recurrence and positivity assumptions imply that S_N
;; and S_0 union {M : M-N is in S_0} are both supported in [1,B+N].
;; Consequently their equality over all integers is equivalent to equality on
;; that finite interval. FROM-TO-BY enumerates the interval, COLLECT$ wraps
;; each integer as the argument list expected by ALWAYS$+, and N is carried in
;; ALWAYS$+'s globals list.

(defun putnam-2000-b5-singleton-function ()
  '(lambda (m)
     (cons m 'nil)))

(defun putnam-2000-b5-index-range-term (upper)
  (list
   'from-to-by
   (putnam-2000-b5-quoted 1)
   upper
   (putnam-2000-b5-quoted 1)))

(defun putnam-2000-b5-membership-equality-function
    (sequence)
  (let* ((index
          (list 'car 'globals))
         (element
          (list 'car 'entry))
         (left-member
          (putnam-2000-b5-member-term
           sequence index element))
         (initial-member
          (putnam-2000-b5-member-term
           sequence
           (putnam-2000-b5-quoted 0)
           element))
         (shifted-element
          (list
           'binary-+
           element
           (list 'unary-- index)))
         (shifted-member
          (putnam-2000-b5-member-term
           sequence
           (putnam-2000-b5-quoted 0)
           shifted-element))
         (union-member
          (list
           'if
           initial-member
           (putnam-2000-b5-quoted t)
           shifted-member)))
    (list
     'lambda
     '(globals entry)
     (list 'equal left-member union-member))))

(defun putnam-2000-b5-finite-equality-term
    (equality-function singleton-function support-bound)
  (let* ((upper
          (list 'binary-+ support-bound 'n))
         (range
          (putnam-2000-b5-index-range-term upper))
         (wrapped-range
          (list
           'collect$
           (putnam-2000-b5-quoted singleton-function)
           range))
         (globals
          (putnam-2000-b5-term-list (list 'n))))
    (list
     'always$+
     (putnam-2000-b5-quoted equality-function)
     globals
     wrapped-range)))

(defun putnam-2000-b5-success-function
    (sequence lower-bound)
  (let* ((support-bound
          (putnam-2000-b5-quoted
           (putnam-2000-b5-support-bound sequence)))
         (equality-function
          (putnam-2000-b5-membership-equality-function
           sequence))
         (singleton-function
          (putnam-2000-b5-singleton-function))
         (finite-equality
          (putnam-2000-b5-finite-equality-term
           equality-function
           singleton-function
           support-bound)))
    (list
     'lambda
     '(n)
     (putnam-2000-b5-and-terms
      (list
       (list 'natp 'n)
       (putnam-2000-b5-less-equal-term
        (putnam-2000-b5-quoted lower-bound)
        'n)
       finite-equality)))))

(defun putnam-2000-b5-false-function ()
  '(lambda (n) 'nil))

;; For a natural LOWER-BOUND, SUCCESS-FUNCTION is true exactly at the natural
;; indices N at least LOWER-BOUND satisfying the required set equality.
;; Negated FN-EQUAL against the constantly false unary function is therefore
;; the source's internal unbounded existential quantifier over N.

(defun putnam-2000-b5-conclusion-p (sequence lower-bound)
  (if (putnam-2000-b5-empty-sequence-p sequence)
      t
    (let ((equality-function
           (putnam-2000-b5-membership-equality-function
            sequence))
          (singleton-function
           (putnam-2000-b5-singleton-function))
          (success-function
           (putnam-2000-b5-success-function
            sequence lower-bound))
          (false-function
           (putnam-2000-b5-false-function)))
      (and
       (tamep-functionp equality-function)
       (tamep-functionp singleton-function)
       (tamep-functionp success-function)
       (tamep-functionp false-function)
       (not
        (fn-equal success-function false-function))))))

(defun putnambench-putnam-2000-b5-statement
    (sequence lower-bound)
  (implies
   (and
    (natp lower-bound)
    (tamep-functionp sequence)
    (putnam-2000-b5-finite-initial-p sequence)
    (putnam-2000-b5-positive-p sequence)
    (putnam-2000-b5-recurrence-p sequence))
   (putnam-2000-b5-conclusion-p
    sequence lower-bound)))

(value-triple :itpeval-statement-checked)
:q
