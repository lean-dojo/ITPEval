;; Statement-only formalization of VERINA corpus artifact verina_advanced_68,
;; "runLengthEncoder": a deterministic Unicode-string run-length encoder for
;; digit-free input, together with format, decoding, and emptiness correctness.
;; This file contains no proof.

(in-package "ACL2")

;; A Lean String is canonically represented by its finite list of Unicode
;; scalar values. This preserves the full Char domain rather than restricting
;; strings to ACL2's host character set.

(defun verina-advanced-68-unicode-scalar-p (c)
  (and
   (natp c)
   (or
    (< c 55296)
    (and
     (< 57343 c)
     (< c 1114112)))))

(defun verina-advanced-68-string-p (s)
  (declare (xargs :measure (acl2-count s)))
  (if (consp s)
      (and
       (verina-advanced-68-unicode-scalar-p (car s))
       (verina-advanced-68-string-p (cdr s)))
    (equal s nil)))

;; Lean Char.isDigit recognizes the ASCII scalar values U+0030 through U+0039.

(defun verina-advanced-68-digit-p (c)
  (and
   (natp c)
   (<= 48 c)
   (<= c 57)))

;; This recursion is String.all (fun c => not c.isDigit), the exact source
;; precondition excluding ambiguous digit characters from the input.

(defun verina-advanced-68-run-length-encoder-precond (input)
  (declare (xargs :measure (acl2-count input)))
  (if (consp input)
      (and
       (not (verina-advanced-68-digit-p (car input)))
       (verina-advanced-68-run-length-encoder-precond
        (cdr input)))
    t))

;; The source numToString recursively emits the ordinary most-significant-first
;; decimal digits. Fuel starts above N, while every recursive call divides N
;; by ten, so it adds no cutoff to the source computation.

(defun verina-advanced-68-num-to-string-go (n fuel)
  (declare (xargs :measure (nfix fuel)))
  (if (or
       (not (natp n))
       (zp fuel))
      nil
    (if (< n 10)
        (list (+ n 48))
      (append
       (verina-advanced-68-num-to-string-go
        (floor n 10)
        (- fuel 1))
       (list (+ (mod n 10) 48))))))

(defun verina-advanced-68-num-to-string (n)
  (if (natp n)
      (verina-advanced-68-num-to-string-go
       n
       (+ n 1))
    nil))

;; NIL represents Option.none and a Unicode scalar represents Option.some.
;; Because Unicode scalars are natural numbers, this representation is
;; disjoint. The recursion is exactly the source-local encode function.

(defun verina-advanced-68-encode
    (remaining current-char count)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (let ((c (car remaining))
            (rest (cdr remaining)))
        (if (equal current-char nil)
            (verina-advanced-68-encode rest c 1)
          (if (equal c current-char)
              (verina-advanced-68-encode
               rest
               current-char
               (+ count 1))
            (append
             (cons
              current-char
              (verina-advanced-68-num-to-string count))
             (verina-advanced-68-encode rest c 1)))))
    (if (equal current-char nil)
        nil
      (cons
       current-char
       (verina-advanced-68-num-to-string count)))))

;; Under the canonical representation, String.data and String.mk are identity
;; conversions between a represented string and its scalar list. The
;; proof-valued precondition argument is computationally irrelevant.

(defun verina-advanced-68-run-length-encoder (input)
  (if (equal input nil)
      nil
    (verina-advanced-68-encode
     (cdr input)
     (car input)
     1)))

;; A parsed Lean (Char x Nat) pair is represented by the dotted pair
;; (character . count). ACC stores completed pairs in reverse order, exactly as
;; in the source parseState helper.

(defun verina-advanced-68-parse-state
    (remaining current-char current-count acc)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (let ((c (car remaining))
            (cs (cdr remaining)))
        (if (verina-advanced-68-digit-p c)
            (if (equal current-char nil)
                nil
              (let* ((digit (- c 48))
                     (new-count
                      (if (equal current-count nil)
                          digit
                        (+ (* current-count 10) digit))))
                (verina-advanced-68-parse-state
                 cs
                 current-char
                 new-count
                 acc)))
          (let ((new-acc
                 (if (and
                      (not (equal current-char nil))
                      (not (equal current-count nil)))
                     (cons
                      (cons current-char current-count)
                      acc)
                   acc)))
            (verina-advanced-68-parse-state
             cs
             c
             nil
             new-acc))))
    (reverse
     (if (and
          (not (equal current-char nil))
          (not (equal current-count nil)))
         (cons
          (cons current-char current-count)
          acc)
       acc))))

(defun verina-advanced-68-parse-encoded-string (result)
  (verina-advanced-68-parse-state
   result
   nil
   nil
   nil))

;; This is the source checkPairs recursion. NOW-DIGIT records that the previous
;; position was in a decimal count; a new character must be followed
;; immediately by at least one digit.

(defun verina-advanced-68-format-valid-p
    (characters now-digit)
  (declare (xargs :measure (acl2-count characters)))
  (if (consp characters)
      (let ((c (car characters))
            (cs (cdr characters)))
        (if (and
             now-digit
             (verina-advanced-68-digit-p c))
            (verina-advanced-68-format-valid-p cs t)
          (if (consp cs)
              (if (verina-advanced-68-digit-p (car cs))
                  (verina-advanced-68-format-valid-p
                   (cdr cs)
                   t)
                nil)
            nil)))
    t))

;; These helpers reproduce List.replicate and List.flatMap from the content
;; validation in the source postcondition.

(defun verina-advanced-68-replicate-char (count c)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons
     c
     (verina-advanced-68-replicate-char
      (- count 1)
      c))))

(defun verina-advanced-68-expand-pairs (pairs)
  (declare (xargs :measure (acl2-count pairs)))
  (if (consp pairs)
      (append
       (verina-advanced-68-replicate-char
        (cdr (car pairs))
        (car (car pairs)))
       (verina-advanced-68-expand-pairs (cdr pairs)))
    nil))

(defun verina-advanced-68-run-length-encoder-postcond
    (input result)
  (let* ((pairs
          (verina-advanced-68-parse-encoded-string result))
         (expanded
          (verina-advanced-68-expand-pairs pairs))
         (format-valid
          (verina-advanced-68-format-valid-p result nil))
         (content-valid
          (equal expanded input))
         (nonempty-valid
          (equal
           (equal input nil)
           (equal result nil))))
    (and
     (verina-advanced-68-string-p input)
     (verina-advanced-68-string-p result)
     format-valid
     content-valid
     nonempty-valid)))

;; This predicate is the unproved final correctness proposition connecting the
;; exact precondition and postcondition to the exact executable result.

(defun
    verina-advanced-68-run-length-encoder-spec-satisfied-statement
    (input)
  (implies
   (and
    (verina-advanced-68-string-p input)
    (verina-advanced-68-run-length-encoder-precond input))
   (verina-advanced-68-run-length-encoder-postcond
    input
    (verina-advanced-68-run-length-encoder input))))

(value-triple :itpeval-statement-checked)
:q
