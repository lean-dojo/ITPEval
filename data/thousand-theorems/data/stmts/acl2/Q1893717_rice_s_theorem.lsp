;; Statement-only formalization of thousand-theorems corpus artifact Q1893717,
;; "Rice's theorem": a computable extensional property of partial-recursive
;; unary natural-number functions that holds for one such function holds for
;; every such function. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Natural numbers are decoded exactly as Nat.Partrec.Code: 0, 1, 2, and 3
;; are the base codes, and the two low bits above 3 select pair, composition,
;; primitive recursion, or minimization. The bounded evaluator represents the
;; corresponding partial function; existence of a fuel is definedness.

(defun q1893717-nat-pair (left right)
  (let ((left (nfix left))
        (right (nfix right)))
    (if (< left right)
        (+ (* right right) left)
      (+ (* left left) left right))))

(defun q1893717-isqrt-down (number candidate)
  (declare (xargs :measure (nfix candidate)))
  (if (zp candidate)
      0
    (if (<= (* candidate candidate) number)
        candidate
      (q1893717-isqrt-down number (- candidate 1)))))

(defun q1893717-isqrt (number)
  (let ((number (nfix number)))
    (q1893717-isqrt-down number number)))

(defun q1893717-nat-unpair (number)
  (let* ((number (nfix number))
         (root (q1893717-isqrt number))
         (remainder (- number (* root root))))
    (if (< remainder root)
        (cons remainder root)
      (cons root (- remainder root)))))

(defun q1893717-code-decode-aux (steps number)
  (declare (xargs :measure (nfix steps)))
  (if (zp steps)
      :zero
    (let ((number (nfix number)))
      (cond
       ((equal number 0) :zero)
       ((equal number 1) :succ)
       ((equal number 2) :left)
       ((equal number 3) :right)
       (t
        (let* ((payload (- number 4))
               (low-bit (mod payload 2))
               (high-bit (mod (floor payload 2) 2))
               (subcode-pair-number (floor payload 4))
               (subcode-pair
                (q1893717-nat-unpair subcode-pair-number))
               (next-steps (- steps 1)))
          (cond
           ((and (equal low-bit 0)
                 (equal high-bit 0))
            (list
             :pair
             (q1893717-code-decode-aux
              next-steps (car subcode-pair))
             (q1893717-code-decode-aux
              next-steps (cdr subcode-pair))))
           ((and (equal low-bit 0)
                 (equal high-bit 1))
            (list
             :comp
             (q1893717-code-decode-aux
              next-steps (car subcode-pair))
             (q1893717-code-decode-aux
              next-steps (cdr subcode-pair))))
           ((and (equal low-bit 1)
                 (equal high-bit 0))
            (list
             :prec
             (q1893717-code-decode-aux
              next-steps (car subcode-pair))
             (q1893717-code-decode-aux
              next-steps (cdr subcode-pair))))
           (t
            (list
             :rfind
             (q1893717-code-decode-aux
              next-steps subcode-pair-number))))))))))

(defun q1893717-code-decode (number)
  (q1893717-code-decode-aux
   (+ 1 (nfix number))
   number))

(defun q1893717-some (value)
  (cons :some value))

(defun q1893717-some-p (result)
  (and (consp result)
       (equal (car result) :some)
       (natp (cdr result))))

(defun q1893717-evaln-measure (fuel code)
  (make-ord
   1
   (+ 1 (nfix fuel))
   (acl2-count code)))

(defun q1893717-evaln (fuel code input)
  (declare
   (xargs
    :measure (q1893717-evaln-measure fuel code)
    :well-founded-relation o<))
  (if (zp fuel)
      nil
    (let ((bound (- fuel 1)))
      (if (or (not (natp input))
              (< bound input))
          nil
        (cond
         ((equal code :zero)
          (q1893717-some 0))
         ((equal code :succ)
          (q1893717-some (+ input 1)))
         ((equal code :left)
          (q1893717-some
           (car (q1893717-nat-unpair input))))
         ((equal code :right)
          (q1893717-some
           (cdr (q1893717-nat-unpair input))))
         ((and (consp code)
               (equal (car code) :pair))
          (let ((left
                 (q1893717-evaln
                  fuel (cadr code) input)))
            (if (q1893717-some-p left)
                (let ((right
                       (q1893717-evaln
                        fuel (caddr code) input)))
                  (if (q1893717-some-p right)
                      (q1893717-some
                       (q1893717-nat-pair
                        (cdr left) (cdr right)))
                    nil))
              nil)))
         ((and (consp code)
               (equal (car code) :comp))
          (let ((argument
                 (q1893717-evaln
                  fuel (caddr code) input)))
            (if (q1893717-some-p argument)
                (q1893717-evaln
                 fuel (cadr code) (cdr argument))
              nil)))
         ((and (consp code)
               (equal (car code) :prec))
          (let* ((arguments
                  (q1893717-nat-unpair input))
                 (parameter (car arguments))
                 (counter (cdr arguments)))
            (if (zp counter)
                (q1893717-evaln
                 fuel (cadr code) parameter)
              (let* ((predecessor (- counter 1))
                     (previous
                      (q1893717-evaln
                       bound
                       code
                       (q1893717-nat-pair
                        parameter predecessor))))
                (if (q1893717-some-p previous)
                    (q1893717-evaln
                     fuel
                     (caddr code)
                     (q1893717-nat-pair
                      parameter
                      (q1893717-nat-pair
                       predecessor
                       (cdr previous))))
                  nil)))))
         ((and (consp code)
               (equal (car code) :rfind))
          (let* ((arguments
                  (q1893717-nat-unpair input))
                 (parameter (car arguments))
                 (start (cdr arguments))
                 (test
                  (q1893717-evaln
                   fuel
                   (cadr code)
                   (q1893717-nat-pair
                    parameter start))))
            (if (q1893717-some-p test)
                (if (equal (cdr test) 0)
                    (q1893717-some start)
                  (q1893717-evaln
                   bound
                   code
                   (q1893717-nat-pair
                    parameter (+ start 1))))
              nil)))
         (t nil))))))

;; DEFUN-SK supplies the source's unbounded quantifiers. Natural-number
;; conditions recover the source domains, while existential fuel and decider
;; witnesses remain internal. The generic membership predicate represents an
;; arbitrary class of program codes; extensionality below makes it descend to
;; a set of partial functions.

(defstub q1893717-class-member (class program) t)

(defun q1893717-class-member-p (class program)
  (if (q1893717-class-member class program)
      t
    nil))

(defun-sk q1893717-halts-with-p
    (program input output)
  (exists (fuel)
    (and
     (natp program)
     (natp input)
     (natp output)
     (natp fuel)
     (equal
      (q1893717-evaln
       fuel
       (q1893717-code-decode program)
       input)
      (q1893717-some output)))))

(defun-sk q1893717-program-graph-equal-p
    (left-program right-program)
  (forall (input output)
    (implies
     (and
      (natp input)
      (natp output))
     (iff
      (q1893717-halts-with-p
       left-program input output)
      (q1893717-halts-with-p
       right-program input output)))))

(defun q1893717-program-equivalent-p
    (left-program right-program)
  (and
   (natp left-program)
   (natp right-program)
   (q1893717-program-graph-equal-p
    left-program right-program)))

;; A class of codes represents a set of partial functions exactly when it is
;; invariant under equality of the partial input/output relations.

(defun-sk q1893717-extensional-class-p (class)
  (forall (left-program right-program)
    (implies
     (and
      (natp left-program)
      (natp right-program)
      (q1893717-program-equivalent-p
       left-program right-program))
     (iff
      (q1893717-class-member-p class left-program)
      (q1893717-class-member-p class right-program)))))

;; A decider program is total on program codes and returns the canonical
;; Boolean encoding 1 exactly on members and 0 exactly on nonmembers.

(defun q1893717-decider-entry-p
    (class decider program)
  (if (q1893717-class-member-p class program)
      (q1893717-halts-with-p decider program 1)
    (q1893717-halts-with-p decider program 0)))

(defun-sk q1893717-decider-law-p (class decider)
  (forall (program)
    (implies
     (natp program)
     (q1893717-decider-entry-p
      class decider program))))

(defun q1893717-total-decider-p (class decider)
  (and
   (natp decider)
   (q1893717-decider-law-p class decider)))

(defun-sk q1893717-computable-class-p (class)
  (exists (decider)
    (q1893717-total-decider-p class decider)))

(defun thousand-theorems-q1893717-rice-theorem-statement
    (class f-program g-program)
  (implies
   (and
    (q1893717-extensional-class-p class)
    (q1893717-computable-class-p class)
    (natp f-program)
    (natp g-program)
    (q1893717-class-member-p class f-program))
   (q1893717-class-member-p class g-program)))

(value-triple :itpeval-statement-checked)
:q
