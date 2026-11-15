;; Statement-only formalization of thousand-theorems corpus artifact Q1933521,
;; "Kleene's recursion theorem": every partial-recursive binary program has a
;; program whose unary partial evaluation equals the binary program applied to
;; its own code and the same input. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Codes are transported along the source's denumeration Code <-> Nat.  The
;; decoder below follows ofNatCode: 0, 1, 2, and 3 are the four base codes,
;; while the two low bits above 3 select pair, composition, primitive
;; recursion, or minimization.  The bounded recursion is extensionally the
;; source decoder because every recursive code number is smaller than its
;; parent.

(defun q1933521-nat-pair (left right)
  (let ((left (nfix left))
        (right (nfix right)))
    (if (< left right)
        (+ (* right right) left)
      (+ (* left left) left right))))

(defun q1933521-isqrt-down (number candidate)
  (declare (xargs :measure (nfix candidate)))
  (if (zp candidate)
      0
    (if (<= (* candidate candidate) number)
        candidate
      (q1933521-isqrt-down number (- candidate 1)))))

(defun q1933521-isqrt (number)
  (let ((number (nfix number)))
    (q1933521-isqrt-down number number)))

(defun q1933521-nat-unpair (number)
  (let* ((number (nfix number))
         (root (q1933521-isqrt number))
         (remainder (- number (* root root))))
    (if (< remainder root)
        (cons remainder root)
      (cons root (- remainder root)))))

(defun q1933521-code-decode-aux (steps number)
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
                (q1933521-nat-unpair subcode-pair-number))
               (next-steps (- steps 1)))
          (cond
           ((and (equal low-bit 0)
                 (equal high-bit 0))
            (list
             :pair
             (q1933521-code-decode-aux
              next-steps (car subcode-pair))
             (q1933521-code-decode-aux
              next-steps (cdr subcode-pair))))
           ((and (equal low-bit 0)
                 (equal high-bit 1))
            (list
             :comp
             (q1933521-code-decode-aux
              next-steps (car subcode-pair))
             (q1933521-code-decode-aux
              next-steps (cdr subcode-pair))))
           ((and (equal low-bit 1)
                 (equal high-bit 0))
            (list
             :prec
             (q1933521-code-decode-aux
              next-steps (car subcode-pair))
             (q1933521-code-decode-aux
              next-steps (cdr subcode-pair))))
           (t
            (list
             :rfind
             (q1933521-code-decode-aux
              next-steps subcode-pair-number))))))))))

(defun q1933521-code-decode (number)
  (q1933521-code-decode-aux
   (+ 1 (nfix number))
   number))

;; A successful bounded evaluation is (:some . value); NIL is undefined.
;; This is the source evaln definition, including its input bound.  Recursive
;; calls either decrease the fuel or move to a proper subcode.

(defun q1933521-some (value)
  (cons :some value))

(defun q1933521-some-p (result)
  (and (consp result)
       (equal (car result) :some)
       (natp (cdr result))))

(defun q1933521-evaln-measure (fuel code)
  (make-ord
   1
   (+ 1 (nfix fuel))
   (acl2-count code)))

(defun q1933521-evaln (fuel code input)
  (declare
   (xargs
    :measure (q1933521-evaln-measure fuel code)
    :well-founded-relation o<))
  (if (zp fuel)
      nil
    (let ((bound (- fuel 1)))
      (if (or (not (natp input))
              (< bound input))
          nil
        (cond
         ((equal code :zero)
          (q1933521-some 0))
         ((equal code :succ)
          (q1933521-some (+ input 1)))
         ((equal code :left)
          (q1933521-some
           (car (q1933521-nat-unpair input))))
         ((equal code :right)
          (q1933521-some
           (cdr (q1933521-nat-unpair input))))
         ((and (consp code)
               (equal (car code) :pair))
          (let ((left
                 (q1933521-evaln
                  fuel (cadr code) input)))
            (if (q1933521-some-p left)
                (let ((right
                       (q1933521-evaln
                        fuel (caddr code) input)))
                  (if (q1933521-some-p right)
                      (q1933521-some
                       (q1933521-nat-pair
                        (cdr left) (cdr right)))
                    nil))
              nil)))
         ((and (consp code)
               (equal (car code) :comp))
          (let ((argument
                 (q1933521-evaln
                  fuel (caddr code) input)))
            (if (q1933521-some-p argument)
                (q1933521-evaln
                 fuel (cadr code) (cdr argument))
              nil)))
         ((and (consp code)
               (equal (car code) :prec))
          (let* ((arguments
                  (q1933521-nat-unpair input))
                 (parameter (car arguments))
                 (counter (cdr arguments)))
            (if (zp counter)
                (q1933521-evaln
                 fuel (cadr code) parameter)
              (let* ((predecessor (- counter 1))
                     (previous
                      (q1933521-evaln
                       bound
                       code
                       (q1933521-nat-pair
                        parameter predecessor))))
                (if (q1933521-some-p previous)
                    (q1933521-evaln
                     fuel
                     (caddr code)
                     (q1933521-nat-pair
                      parameter
                      (q1933521-nat-pair
                       predecessor
                       (cdr previous))))
                  nil)))))
         ((and (consp code)
               (equal (car code) :rfind))
          (let* ((arguments
                  (q1933521-nat-unpair input))
                 (parameter (car arguments))
                 (start (cdr arguments))
                 (test
                  (q1933521-evaln
                   fuel
                   (cadr code)
                   (q1933521-nat-pair
                    parameter start))))
            (if (q1933521-some-p test)
                (if (equal (cdr test) 0)
                    (q1933521-some start)
                  (q1933521-evaln
                   bound
                   code
                   (q1933521-nat-pair
                    parameter (+ start 1))))
              nil)))
         (t nil))))))

;; DEFUN-SK supplies the source's unbounded quantifiers. Existence of a fuel is
;; termination of the corresponding partial evaluation; agreement for every
;; natural output is equality of deterministic partial values, including
;; divergence.

(defun-sk q1933521-halts-with-p
    (program input output)
  (exists (fuel)
    (and
     (natp program)
     (natp input)
     (natp output)
     (natp fuel)
     (equal
      (q1933521-evaln
       fuel
       (q1933521-code-decode program)
       input)
      (q1933521-some output)))))

(defun-sk q1933521-partial-equal-p
    (left-program left-input right-program right-input)
  (forall (output)
    (implies
     (natp output)
     (iff
      (q1933521-halts-with-p
       left-program left-input output)
      (q1933521-halts-with-p
       right-program right-input output)))))

;; A natural number denotes a source Code through the exact denumeration above.
;; Thus a binary program denotes a Partrec2 function of a program code and an
;; input. The fixed-program witness remains existentially quantified inside
;; the statement, and the input law compares both defined values and
;; divergence at every natural-number input.

(defun-sk q1933521-fixed-point-input-law-p
    (functional-program fixed-program)
  (forall (input)
    (implies
     (natp input)
     (q1933521-partial-equal-p
      fixed-program
      input
      functional-program
      (q1933521-nat-pair fixed-program input)))))

(defun-sk q1933521-fixed-program-exists-p (functional-program)
  (exists (fixed-program)
    (and
     (natp fixed-program)
     (q1933521-fixed-point-input-law-p
      functional-program fixed-program))))

(defun thousand-theorems-q1933521-kleene-recursion-theorem-statement
    (functional-program)
  (implies
   (natp functional-program)
   (q1933521-fixed-program-exists-p functional-program)))

(value-triple :itpeval-statement-checked)
:q
