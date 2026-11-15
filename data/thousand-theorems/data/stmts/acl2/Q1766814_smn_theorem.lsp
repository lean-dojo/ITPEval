;; Statement-only formalization of thousand-theorems corpus artifact Q1766814,
;; "Smn theorem": there exists a total computable program transformer that
;; fixes the first natural-number argument of every partial-recursive program.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Codes are transported along the source's denumeration Code <-> Nat.  The
;; decoder below follows ofNatCode: 0, 1, 2, and 3 are the four base codes,
;; while the two low bits above 3 select pair, composition, primitive
;; recursion, or minimization.  The bounded recursion is extensionally the
;; source decoder because every recursive code number is smaller than its
;; parent.

(defun q1766814-nat-pair (left right)
  (let ((left (nfix left))
        (right (nfix right)))
    (if (< left right)
        (+ (* right right) left)
      (+ (* left left) left right))))

(defun q1766814-isqrt-down (number candidate)
  (declare (xargs :measure (nfix candidate)))
  (if (zp candidate)
      0
    (if (<= (* candidate candidate) number)
        candidate
      (q1766814-isqrt-down number (- candidate 1)))))

(defun q1766814-isqrt (number)
  (let ((number (nfix number)))
    (q1766814-isqrt-down number number)))

(defun q1766814-nat-unpair (number)
  (let* ((number (nfix number))
         (root (q1766814-isqrt number))
         (remainder (- number (* root root))))
    (if (< remainder root)
        (cons remainder root)
      (cons root (- remainder root)))))

(defun q1766814-code-decode-aux (steps number)
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
                (q1766814-nat-unpair subcode-pair-number))
               (next-steps (- steps 1)))
          (cond
           ((and (equal low-bit 0)
                 (equal high-bit 0))
            (list
             :pair
             (q1766814-code-decode-aux
              next-steps (car subcode-pair))
             (q1766814-code-decode-aux
              next-steps (cdr subcode-pair))))
           ((and (equal low-bit 0)
                 (equal high-bit 1))
            (list
             :comp
             (q1766814-code-decode-aux
              next-steps (car subcode-pair))
             (q1766814-code-decode-aux
              next-steps (cdr subcode-pair))))
           ((and (equal low-bit 1)
                 (equal high-bit 0))
            (list
             :prec
             (q1766814-code-decode-aux
              next-steps (car subcode-pair))
             (q1766814-code-decode-aux
              next-steps (cdr subcode-pair))))
           (t
            (list
             :rfind
             (q1766814-code-decode-aux
              next-steps subcode-pair-number))))))))))

(defun q1766814-code-decode (number)
  (q1766814-code-decode-aux
   (+ 1 (nfix number))
   number))

;; A successful bounded evaluation is (:some . value); NIL is undefined.
;; This is the source evaln definition, including its input bound.  Recursive
;; calls either decrease the fuel or move to a proper subcode.

(defun q1766814-some (value)
  (cons :some value))

(defun q1766814-some-p (result)
  (and (consp result)
       (equal (car result) :some)
       (natp (cdr result))))

(defun q1766814-evaln-measure (fuel code)
  (make-ord
   1
   (+ 1 (nfix fuel))
   (acl2-count code)))

(defun q1766814-evaln (fuel code input)
  (declare
   (xargs
    :measure (q1766814-evaln-measure fuel code)
    :well-founded-relation o<))
  (if (zp fuel)
      nil
    (let ((bound (- fuel 1)))
      (if (or (not (natp input))
              (< bound input))
          nil
        (cond
         ((equal code :zero)
          (q1766814-some 0))
         ((equal code :succ)
          (q1766814-some (+ input 1)))
         ((equal code :left)
          (q1766814-some
           (car (q1766814-nat-unpair input))))
         ((equal code :right)
          (q1766814-some
           (cdr (q1766814-nat-unpair input))))
         ((and (consp code)
               (equal (car code) :pair))
          (let ((left
                 (q1766814-evaln
                  fuel (cadr code) input)))
            (if (q1766814-some-p left)
                (let ((right
                       (q1766814-evaln
                        fuel (caddr code) input)))
                  (if (q1766814-some-p right)
                      (q1766814-some
                       (q1766814-nat-pair
                        (cdr left) (cdr right)))
                    nil))
              nil)))
         ((and (consp code)
               (equal (car code) :comp))
          (let ((argument
                 (q1766814-evaln
                  fuel (caddr code) input)))
            (if (q1766814-some-p argument)
                (q1766814-evaln
                 fuel (cadr code) (cdr argument))
              nil)))
         ((and (consp code)
               (equal (car code) :prec))
          (let* ((arguments
                  (q1766814-nat-unpair input))
                 (parameter (car arguments))
                 (counter (cdr arguments)))
            (if (zp counter)
                (q1766814-evaln
                 fuel (cadr code) parameter)
              (let* ((predecessor (- counter 1))
                     (previous
                      (q1766814-evaln
                       bound
                       code
                       (q1766814-nat-pair
                        parameter predecessor))))
                (if (q1766814-some-p previous)
                    (q1766814-evaln
                     fuel
                     (caddr code)
                     (q1766814-nat-pair
                      parameter
                      (q1766814-nat-pair
                       predecessor
                       (cdr previous))))
                  nil)))))
         ((and (consp code)
               (equal (car code) :rfind))
          (let* ((arguments
                  (q1766814-nat-unpair input))
                 (parameter (car arguments))
                 (start (cdr arguments))
                 (test
                  (q1766814-evaln
                   fuel
                   (cadr code)
                   (q1766814-nat-pair
                    parameter start))))
            (if (q1766814-some-p test)
                (if (equal (cdr test) 0)
                    (q1766814-some start)
                  (q1766814-evaln
                   bound
                   code
                   (q1766814-nat-pair
                    parameter (+ start 1))))
              nil)))
         (t nil))))))

;; DEFUN-SK keeps the source's unbounded quantifiers internal.  Existence of a
;; fuel is termination of the corresponding partial evaluation; agreement for
;; every possible natural output is equality of partial values.

(defun-sk q1766814-halts-with-p
    (program input output)
  (exists (fuel)
    (and
     (natp program)
     (natp input)
     (natp output)
     (natp fuel)
     (equal
      (q1766814-evaln
       fuel
       (q1766814-code-decode program)
       input)
      (q1766814-some output)))))

(defun-sk q1766814-partial-equal-p
    (left-program left-input right-program right-input)
  (forall (output)
    (implies
     (natp output)
     (iff
      (q1766814-halts-with-p
       left-program left-input output)
      (q1766814-halts-with-p
       right-program right-input output)))))

;; A transformer program receives pair(code-number,n) and returns the code
;; number for f c n.  Totality and the S-m-n evaluation equation remain inside
;; the quantified statement.  Since every natural decodes to a partial-
;; recursive Code, an internally quantified total transformer program is
;; equivalent to the source's existential Computable2 function.

(defun-sk q1766814-output-program-law-p
    (output-program source-program fixed-input)
  (forall (input)
    (implies
     (natp input)
     (q1766814-partial-equal-p
      output-program
      input
      source-program
      (q1766814-nat-pair fixed-input input)))))

(defun q1766814-output-program-valid-p
    (transformer source-program fixed-input output-program)
  (and
   (natp output-program)
   (q1766814-halts-with-p
    transformer
    (q1766814-nat-pair
     source-program fixed-input)
    output-program)
   (q1766814-output-program-law-p
    output-program source-program fixed-input)))

(defun-sk q1766814-transformer-entry-p
    (transformer source-program fixed-input)
  (exists (output-program)
    (q1766814-output-program-valid-p
     transformer source-program fixed-input output-program)))

(defun-sk q1766814-total-smn-transformer-p (transformer)
  (forall (source-program fixed-input)
    (implies
     (and
      (natp source-program)
      (natp fixed-input))
     (q1766814-transformer-entry-p
      transformer source-program fixed-input))))

(defun-sk thousand-theorems-q1766814-smn-theorem-statement ()
  (exists (transformer)
    (and
     (natp transformer)
     (q1766814-total-smn-transformer-p transformer))))

(value-triple :itpeval-statement-checked)
:q
