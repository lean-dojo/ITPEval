;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/verker/strpbrk_Why3_ide_VCstrpbrk_loop_term_2_positive_goal18:
;; the current first-string offset is at most the second string's start
;; offset plus its logical length, under the stated strpbrk, valid-string,
;; address-order, membership, and quantified no-match hypotheses.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun spg18-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun spg18-address-base (address)
  (car address))

(defun spg18-address-offset (address)
  (cdr address))

(defun spg18-shift (address amount)
  (cons
   (spg18-address-base address)
   (+ (spg18-address-offset address)
      amount)))

(defun spg18-null-address ()
  (cons 0 0))

;; Conservative interfaces represent the universally arbitrary character
;; memory t_1 and allocation map t, together with the source's region,
;; address-order, logical strlen, logical strpbrk, unsigned conversion,
;; linkedness, and constancy symbols.

(defstub spg18-character-memory (address) t)
(defstub spg18-allocation (index) t)
(defstub spg18-region (base) t)
(defstub spg18-addr-le-op (left right) t)
(defstub spg18-addr-lt-op (left right) t)
(defstub spg18-l-strlen (address) t)
(defstub spg18-l-strpbrk (string accept) t)
(defstub spg18-to-uint64 (value) t)
(defstub spg18-linked-op () t)
(defstub spg18-sconst-op () t)

;; Preserve the source function types over the full address and unbounded
;; mathematical-integer domains.

(defun-sk spg18-function-types-p ()
  (forall (address other index base value)
    (and
     (implies
      (spg18-address-p address)
      (and
       (integerp
        (spg18-character-memory address))
       (integerp
        (spg18-l-strlen address))))
     (implies
      (and
       (spg18-address-p address)
       (spg18-address-p other))
      (spg18-address-p
       (spg18-l-strpbrk address other)))
     (implies
      (integerp index)
      (integerp
       (spg18-allocation index)))
     (implies
      (integerp base)
      (integerp
       (spg18-region base)))
     (implies
      (integerp value)
      (integerp
       (spg18-to-uint64 value))))))

(defun spg18-addr-le-p (left right)
  (if (spg18-addr-le-op left right) t nil))

(defun spg18-addr-lt-p (left right)
  (if (spg18-addr-lt-op left right) t nil))

;; On addresses with equal bases, the source address relations are exactly
;; mathematical-integer order on offsets.

(defun-sk spg18-address-order-laws-p ()
  (forall (left right)
    (implies
     (and
      (spg18-address-p left)
      (spg18-address-p right)
      (equal
       (spg18-address-base left)
       (spg18-address-base right)))
     (and
      (equal
       (spg18-addr-le-p left right)
       (<=
        (spg18-address-offset left)
        (spg18-address-offset right)))
      (equal
       (spg18-addr-lt-p left right)
       (<
        (spg18-address-offset left)
        (spg18-address-offset right)))))))

(defun spg18-linked-p ()
  (if (spg18-linked-op) t nil))

(defun spg18-sconst-p ()
  (if (spg18-sconst-op) t nil))

;; Exact mathematical ranges for the source C integer predicates.

(defun spg18-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun spg18-is-uint64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; Universal range, identity-on-range, and projection laws for the source's
;; abstract Cint.to_uint64 operation used by logical strlen.

(defun-sk spg18-to-uint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (spg18-is-uint64-p
       (spg18-to-uint64 value))
      (implies
       (spg18-is-uint64-p value)
       (equal
        (spg18-to-uint64 value)
        value))
      (equal
       (spg18-to-uint64
        (spg18-to-uint64 value))
       (spg18-to-uint64 value))))))

;; Exact unfolding of Memory.valid_rw for the arbitrary allocation map t.

(defun spg18-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0
       (spg18-address-base address))
    (<= 0
        (spg18-address-offset address))
    (<=
     (+ (spg18-address-offset address)
        length)
     (spg18-allocation
      (spg18-address-base address))))))

;; Exact unfolding of A_Strlen.p_valid_str. The terminating position remains
;; an internal existential over all mathematical integers, and its character
;; range condition remains universally quantified over all integers.

(defun-sk spg18-string-chars-sint8-through-p
    (address bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position bound)
      (spg18-is-sint8-p
       (spg18-character-memory
        (spg18-shift address position)))))))

(defun-sk spg18-valid-string-p (address)
  (exists (index)
    (and
     (integerp index)
     (equal
      (spg18-character-memory
       (spg18-shift address index))
      0)
     (spg18-is-uint64-p index)
     (spg18-valid-rw-p
      (spg18-shift address 0)
      (+ 1 index))
     (spg18-string-chars-sint8-through-p
      address index))))

;; Universal closures of A_Strlen.fix_l_strlen and Q_TL_strlen.

(defun-sk spg18-strlen-laws-p ()
  (forall (address)
    (implies
     (spg18-address-p address)
     (and
      (if
          (equal
           (spg18-character-memory
            (spg18-shift address 0))
           0)
          (equal
           (spg18-l-strlen address)
           0)
        (equal
         (spg18-to-uint64
          (+ 1
             (spg18-l-strlen
              (spg18-shift address 1))))
         (spg18-l-strlen address)))
      (spg18-is-uint64-p
       (spg18-l-strlen address))))))

;; Exact unfolding of A_StrSpn.p_in_array. Its witness remains existentially
;; quantified over the full source address type.

(defun-sk spg18-in-array-p (start value)
  (exists (candidate)
    (and
     (spg18-address-p candidate)
     (equal
      (spg18-character-memory candidate)
      value)
     (spg18-addr-le-p start candidate)
     (spg18-addr-lt-p
      candidate
      (spg18-shift
       start
       (spg18-l-strlen start))))))

;; Exact universal closures of the three A_StrPBrk axioms.

(defun-sk spg18-strpbrk-laws-p ()
  (forall (string accept)
    (implies
     (and
      (spg18-address-p string)
      (spg18-address-p accept))
     (and
      (implies
       (equal
        (spg18-character-memory string)
        0)
       (equal
        (spg18-l-strpbrk string accept)
        (spg18-null-address)))
      (implies
       (and
        (not
         (equal
          (spg18-character-memory string)
          0))
        (spg18-in-array-p
         accept
         (spg18-character-memory string)))
       (equal
        (spg18-l-strpbrk string accept)
        string))
      (implies
       (and
        (not
         (equal
          (spg18-character-memory string)
          0))
        (not
         (spg18-in-array-p
          accept
          (spg18-character-memory string))))
       (equal
        (spg18-l-strpbrk
         (spg18-shift string 1)
         accept)
        (spg18-l-strpbrk string accept)))))))

;; The source's two quantified no-match hypotheses remain universal over
;; every address rather than being replaced by external witnesses.

(defun-sk spg18-no-x1-before-current-p
    (start current value)
  (forall (candidate)
    (implies
     (spg18-address-p candidate)
     (implies
      (spg18-addr-lt-p candidate current)
      (implies
       (spg18-addr-le-p start candidate)
       (not
        (equal
         value
         (spg18-character-memory candidate))))))))

(defun-sk spg18-cross-values-distinct-p
    (second-start first-start first-current second-end)
  (forall (first-candidate second-candidate)
    (implies
     (and
      (spg18-address-p first-candidate)
      (spg18-address-p second-candidate))
     (implies
      (spg18-addr-lt-p first-candidate first-current)
      (implies
       (spg18-addr-le-p second-start second-candidate)
       (implies
        (spg18-addr-le-p first-start first-candidate)
        (implies
         (spg18-addr-lt-p second-candidate second-end)
         (not
          (equal
           (spg18-character-memory first-candidate)
           (spg18-character-memory second-candidate))))))))))

(defun-sk
    ntp4vc-strpbrk-loop-term-2-positive-goal18-statement
    ()
  (forall
   (a a1 a2 a3)
   (implies
    (and
     (spg18-address-p a)
     (spg18-address-p a1)
     (spg18-address-p a2)
     (spg18-address-p a3)
     (spg18-function-types-p)
     (spg18-address-order-laws-p)
     (spg18-to-uint64-laws-p)
     (spg18-strlen-laws-p)
     (spg18-strpbrk-laws-p))
    (let*
        ((x
          (spg18-character-memory a))
         (x1
          (spg18-character-memory a1))
         (x2
          (spg18-l-strlen a2))
         (a4
          (spg18-shift a2 x2)))
      (implies
       (and
        (not (equal x 0))
        (not (equal x1 0))
        (not (equal x1 x))
        (equal
         (spg18-l-strpbrk a3 a2)
         (spg18-l-strpbrk a1 a2))
        (<=
         (spg18-region
          (spg18-address-base a2))
         0)
        (<=
         (spg18-region
          (spg18-address-base a3))
         0)
        (spg18-linked-p)
        (spg18-sconst-p)
        (spg18-addr-le-p a2 a)
        (spg18-addr-le-p a3 a1)
        (spg18-is-sint8-p x)
        (spg18-is-sint8-p x1)
        (spg18-valid-string-p a)
        (spg18-valid-string-p a1)
        (spg18-valid-string-p a2)
        (spg18-valid-string-p a3)
        (spg18-addr-le-p a a4)
        (spg18-addr-le-p
         a1
         (spg18-shift
          a3
          (spg18-l-strlen a3)))
        (implies
         (spg18-in-array-p a2 x1)
         (spg18-in-array-p a x1))
        (spg18-no-x1-before-current-p
         a2 a x1)
        (spg18-cross-values-distinct-p
         a2 a3 a1 a4))
       (<=
        (spg18-address-offset a)
        (+ (spg18-address-offset a2)
           x2)))))))

(value-triple :itpeval-statement-checked)

:q
