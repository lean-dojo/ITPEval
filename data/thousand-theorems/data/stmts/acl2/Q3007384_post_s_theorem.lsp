;; Statement-only formalization of thousand-theorems corpus artifact Q3007384,
;; "Post's theorem": on any primcodable domain, a decidable predicate is
;; computable exactly when it and its complement are recursively enumerable.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Natural numbers are decoded exactly as Nat.Partrec.Code: 0, 1, 2, and 3
;; are the base codes, and the two low bits above 3 select pair, composition,
;; primitive recursion, or minimization. The bounded evaluator represents the
;; corresponding partial function; existence of a fuel is definedness.

(defun q3007384-nat-pair (left right)
  (let ((left (nfix left))
        (right (nfix right)))
    (if (< left right)
        (+ (* right right) left)
      (+ (* left left) left right))))

(defun q3007384-isqrt-down (number candidate)
  (declare (xargs :measure (nfix candidate)))
  (if (zp candidate)
      0
    (if (<= (* candidate candidate) number)
        candidate
      (q3007384-isqrt-down number (- candidate 1)))))

(defun q3007384-isqrt (number)
  (let ((number (nfix number)))
    (q3007384-isqrt-down number number)))

(defun q3007384-nat-unpair (number)
  (let* ((number (nfix number))
         (root (q3007384-isqrt number))
         (remainder (- number (* root root))))
    (if (< remainder root)
        (cons remainder root)
      (cons root (- remainder root)))))

(defun q3007384-code-decode-aux (steps number)
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
                (q3007384-nat-unpair subcode-pair-number))
               (next-steps (- steps 1)))
          (cond
           ((and (equal low-bit 0)
                 (equal high-bit 0))
            (list
             :pair
             (q3007384-code-decode-aux
              next-steps (car subcode-pair))
             (q3007384-code-decode-aux
              next-steps (cdr subcode-pair))))
           ((and (equal low-bit 0)
                 (equal high-bit 1))
            (list
             :comp
             (q3007384-code-decode-aux
              next-steps (car subcode-pair))
             (q3007384-code-decode-aux
              next-steps (cdr subcode-pair))))
           ((and (equal low-bit 1)
                 (equal high-bit 0))
            (list
             :prec
             (q3007384-code-decode-aux
              next-steps (car subcode-pair))
             (q3007384-code-decode-aux
              next-steps (cdr subcode-pair))))
           (t
            (list
             :rfind
             (q3007384-code-decode-aux
              next-steps subcode-pair-number))))))))))

(defun q3007384-code-decode (number)
  (q3007384-code-decode-aux
   (+ 1 (nfix number))
   number))

;; Codes with no minimization node are exactly the primitive-recursive
;; fragment used to present the encoded image of a Primcodable type.

(defun q3007384-primrec-code-p-aux (steps code)
  (declare (xargs :measure (nfix steps)))
  (if (zp steps)
      nil
    (let ((next-steps (- steps 1)))
      (cond
       ((equal code :zero) t)
       ((equal code :succ) t)
       ((equal code :left) t)
       ((equal code :right) t)
       ((and (consp code)
             (equal (car code) :pair))
        (and
         (q3007384-primrec-code-p-aux
          next-steps (cadr code))
         (q3007384-primrec-code-p-aux
          next-steps (caddr code))))
       ((and (consp code)
             (equal (car code) :comp))
        (and
         (q3007384-primrec-code-p-aux
          next-steps (cadr code))
         (q3007384-primrec-code-p-aux
          next-steps (caddr code))))
       ((and (consp code)
             (equal (car code) :prec))
        (and
         (q3007384-primrec-code-p-aux
          next-steps (cadr code))
         (q3007384-primrec-code-p-aux
          next-steps (caddr code))))
       (t nil)))))

(defun q3007384-primrec-program-p (program)
  (and
   (natp program)
   (let ((code (q3007384-code-decode program)))
     (q3007384-primrec-code-p-aux
      (+ 1 (acl2-count code))
      code))))

(defun q3007384-some (value)
  (cons :some value))

(defun q3007384-some-p (result)
  (and (consp result)
       (equal (car result) :some)
       (natp (cdr result))))

(defun q3007384-evaln-measure (fuel code)
  (make-ord
   1
   (+ 1 (nfix fuel))
   (acl2-count code)))

(defun q3007384-evaln (fuel code input)
  (declare
   (xargs
    :measure (q3007384-evaln-measure fuel code)
    :well-founded-relation o<))
  (if (zp fuel)
      nil
    (let ((bound (- fuel 1)))
      (if (or (not (natp input))
              (< bound input))
          nil
        (cond
         ((equal code :zero)
          (q3007384-some 0))
         ((equal code :succ)
          (q3007384-some (+ input 1)))
         ((equal code :left)
          (q3007384-some
           (car (q3007384-nat-unpair input))))
         ((equal code :right)
          (q3007384-some
           (cdr (q3007384-nat-unpair input))))
         ((and (consp code)
               (equal (car code) :pair))
          (let ((left
                 (q3007384-evaln
                  fuel (cadr code) input)))
            (if (q3007384-some-p left)
                (let ((right
                       (q3007384-evaln
                        fuel (caddr code) input)))
                  (if (q3007384-some-p right)
                      (q3007384-some
                       (q3007384-nat-pair
                        (cdr left) (cdr right)))
                    nil))
              nil)))
         ((and (consp code)
               (equal (car code) :comp))
          (let ((argument
                 (q3007384-evaln
                  fuel (caddr code) input)))
            (if (q3007384-some-p argument)
                (q3007384-evaln
                 fuel (cadr code) (cdr argument))
              nil)))
         ((and (consp code)
               (equal (car code) :prec))
          (let* ((arguments
                  (q3007384-nat-unpair input))
                 (parameter (car arguments))
                 (counter (cdr arguments)))
            (if (zp counter)
                (q3007384-evaln
                 fuel (cadr code) parameter)
              (let* ((predecessor (- counter 1))
                     (previous
                      (q3007384-evaln
                       bound
                       code
                       (q3007384-nat-pair
                        parameter predecessor))))
                (if (q3007384-some-p previous)
                    (q3007384-evaln
                     fuel
                     (caddr code)
                     (q3007384-nat-pair
                      parameter
                      (q3007384-nat-pair
                       predecessor
                       (cdr previous))))
                  nil)))))
         ((and (consp code)
               (equal (car code) :rfind))
          (let* ((arguments
                  (q3007384-nat-unpair input))
                 (parameter (car arguments))
                 (start (cdr arguments))
                 (test
                  (q3007384-evaln
                   fuel
                   (cadr code)
                   (q3007384-nat-pair
                    parameter start))))
            (if (q3007384-some-p test)
                (if (equal (cdr test) 0)
                    (q3007384-some start)
                  (q3007384-evaln
                   bound
                   code
                   (q3007384-nat-pair
                    parameter (+ start 1))))
              nil)))
         (t nil))))))

;; The source's arbitrary Primcodable type is transported along its encoding
;; to a decidable carrier of natural-number codes. The generic carrier and
;; predicate symbols retain the universally arbitrary domain and decidable
;; predicate; tags permit independent presentations without finite tables.

(defstub q3007384-carrier-member (carrier element) t)
(defstub q3007384-predicate (predicate element) t)

(defun q3007384-carrier-member-p (carrier element)
  (if (q3007384-carrier-member carrier element)
      t
    nil))

(defun q3007384-predicate-p (predicate element)
  (if (q3007384-predicate predicate element)
      t
    nil))

;; Existence of fuel is definedness of the exact partial-recursive evaluator.
;; DEFUN-SK keeps every program, fuel, output, and unbounded input quantifier
;; inside the corresponding source notion.

(defun-sk q3007384-halts-with-p
    (program input output)
  (exists (fuel)
    (and
     (natp program)
     (natp input)
     (natp output)
     (natp fuel)
     (equal
      (q3007384-evaln
       fuel
       (q3007384-code-decode program)
       input)
      (q3007384-some output)))))

(defun-sk q3007384-halts-p (program input)
  (exists (output)
    (and
     (natp output)
     (q3007384-halts-with-p
      program input output))))

;; A carrier decider presents the encoded image of the Primcodable domain.
;; It returns the standard Boolean code 1 exactly on the image and 0 off it.

(defun q3007384-carrier-decider-entry-p
    (carrier decider element)
  (if (q3007384-carrier-member-p carrier element)
      (q3007384-halts-with-p decider element 1)
    (q3007384-halts-with-p decider element 0)))

(defun-sk q3007384-carrier-decider-law-p
    (carrier decider)
  (forall (element)
    (implies
     (natp element)
     (q3007384-carrier-decider-entry-p
      carrier decider element))))

(defun q3007384-primcodable-presentation-p
    (carrier carrier-decider)
  (and
   (q3007384-primrec-program-p carrier-decider)
   (q3007384-carrier-decider-law-p
    carrier carrier-decider)))

;; ComputablePred means that one program computes the Boolean indicator on
;; every element of the encoded carrier.

(defun q3007384-predicate-decider-entry-p
    (predicate decider element)
  (if (q3007384-predicate-p predicate element)
      (q3007384-halts-with-p decider element 1)
    (q3007384-halts-with-p decider element 0)))

(defun-sk q3007384-predicate-decider-law-p
    (carrier predicate decider)
  (forall (element)
    (implies
     (and
      (natp element)
      (q3007384-carrier-member-p carrier element))
     (q3007384-predicate-decider-entry-p
      predicate decider element))))

(defun q3007384-predicate-decider-p
    (carrier predicate decider)
  (and
   (natp decider)
   (q3007384-predicate-decider-law-p
    carrier predicate decider)))

(defun-sk q3007384-computable-predicate-p
    (carrier predicate)
  (exists (decider)
    (q3007384-predicate-decider-p
     carrier predicate decider)))

;; REPred is the existence of a partial-recursive program whose domain,
;; restricted to the encoded carrier, is exactly the predicate.

(defun-sk q3007384-re-law-p
    (carrier predicate recognizer)
  (forall (element)
    (implies
     (and
      (natp element)
      (q3007384-carrier-member-p carrier element))
     (iff
      (q3007384-predicate-p predicate element)
      (q3007384-halts-p recognizer element)))))

(defun q3007384-recognizer-p
    (carrier predicate recognizer)
  (and
   (natp recognizer)
   (q3007384-re-law-p
    carrier predicate recognizer)))

(defun-sk q3007384-re-predicate-p
    (carrier predicate)
  (exists (recognizer)
    (q3007384-recognizer-p
     carrier predicate recognizer)))

(defun-sk q3007384-complement-re-law-p
    (carrier predicate recognizer)
  (forall (element)
    (implies
     (and
      (natp element)
      (q3007384-carrier-member-p carrier element))
     (iff
      (not (q3007384-predicate-p predicate element))
      (q3007384-halts-p recognizer element)))))

(defun q3007384-complement-recognizer-p
    (carrier predicate recognizer)
  (and
   (natp recognizer)
   (q3007384-complement-re-law-p
    carrier predicate recognizer)))

(defun-sk q3007384-complement-re-predicate-p
    (carrier predicate)
  (exists (recognizer)
    (q3007384-complement-recognizer-p
     carrier predicate recognizer)))

(defun thousand-theorems-q3007384-post-s-theorem-statement
    (carrier carrier-decider predicate)
  (implies
   (q3007384-primcodable-presentation-p
    carrier carrier-decider)
   (iff
    (q3007384-computable-predicate-p
     carrier predicate)
    (and
     (q3007384-re-predicate-p
      carrier predicate)
     (q3007384-complement-re-predicate-p
      carrier predicate)))))

(value-triple :itpeval-statement-checked)
:q
