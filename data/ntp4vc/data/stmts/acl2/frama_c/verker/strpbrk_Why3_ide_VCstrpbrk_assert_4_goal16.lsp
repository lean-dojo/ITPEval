;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/verker/strpbrk_Why3_ide_VCstrpbrk_assert_4_goal16:
;; distinct bytes occur at two ordered positions under the stated strpbrk
;; equality, valid-string, address-order, membership, and no-match hypotheses.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun spg16-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun spg16-address-base (address)
  (car address))

(defun spg16-address-offset (address)
  (cdr address))

(defun spg16-shift (address amount)
  (cons
   (spg16-address-base address)
   (+ (spg16-address-offset address)
      amount)))

(defun spg16-null-address ()
  (cons 0 0))

;; Conservative interfaces represent the universally arbitrary character
;; memory t_1 and allocation map t, together with the source's region,
;; address-order, logical strlen, logical strpbrk, unsigned conversion,
;; linkedness, and constancy symbols.

(defstub spg16-character-memory (address) t)
(defstub spg16-allocation (index) t)
(defstub spg16-region (base) t)
(defstub spg16-addr-le-op (left right) t)
(defstub spg16-addr-lt-op (left right) t)
(defstub spg16-l-strlen (address) t)
(defstub spg16-l-strpbrk (string accept) t)
(defstub spg16-to-uint64 (value) t)
(defstub spg16-linked-op () t)
(defstub spg16-sconst-op () t)

;; Preserve the source function types over the full address and unbounded
;; mathematical-integer domains.

(defun-sk spg16-function-types-p ()
  (forall (address other index base value)
    (and
     (implies
      (spg16-address-p address)
      (and
       (integerp
        (spg16-character-memory address))
       (integerp
        (spg16-l-strlen address))))
     (implies
      (and
       (spg16-address-p address)
       (spg16-address-p other))
      (spg16-address-p
       (spg16-l-strpbrk address other)))
     (implies
      (integerp index)
      (integerp
       (spg16-allocation index)))
     (implies
      (integerp base)
      (integerp
       (spg16-region base)))
     (implies
      (integerp value)
      (integerp
       (spg16-to-uint64 value))))))

(defun spg16-addr-le-p (left right)
  (if (spg16-addr-le-op left right) t nil))

(defun spg16-addr-lt-p (left right)
  (if (spg16-addr-lt-op left right) t nil))

;; On addresses with equal bases, the source address relations are exactly
;; mathematical-integer order on offsets.

(defun-sk spg16-address-order-laws-p ()
  (forall (left right)
    (implies
     (and
      (spg16-address-p left)
      (spg16-address-p right)
      (equal
       (spg16-address-base left)
       (spg16-address-base right)))
     (and
      (equal
       (spg16-addr-le-p left right)
       (<=
        (spg16-address-offset left)
        (spg16-address-offset right)))
      (equal
       (spg16-addr-lt-p left right)
       (<
        (spg16-address-offset left)
        (spg16-address-offset right)))))))

(defun spg16-linked-p ()
  (if (spg16-linked-op) t nil))

(defun spg16-sconst-p ()
  (if (spg16-sconst-op) t nil))

;; Exact mathematical ranges for the source C integer predicates.

(defun spg16-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun spg16-is-uint64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; Universal range, identity-on-range, and projection laws for the source's
;; abstract Cint.to_uint64 operation used by logical strlen.

(defun-sk spg16-to-uint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (spg16-is-uint64-p
       (spg16-to-uint64 value))
      (implies
       (spg16-is-uint64-p value)
       (equal
        (spg16-to-uint64 value)
        value))
      (equal
       (spg16-to-uint64
        (spg16-to-uint64 value))
       (spg16-to-uint64 value))))))

;; Exact unfolding of Memory.valid_rw for the arbitrary allocation map t.

(defun spg16-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0
       (spg16-address-base address))
    (<= 0
        (spg16-address-offset address))
    (<=
     (+ (spg16-address-offset address)
        length)
     (spg16-allocation
      (spg16-address-base address))))))

;; Exact unfolding of A_Strlen.p_valid_str. The terminating position remains
;; an internal existential over all mathematical integers, and its character
;; range condition remains universally quantified over all integers.

(defun-sk spg16-string-chars-sint8-through-p
    (address bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position bound)
      (spg16-is-sint8-p
       (spg16-character-memory
        (spg16-shift address position)))))))

(defun-sk spg16-valid-string-p (address)
  (exists (index)
    (and
     (integerp index)
     (equal
      (spg16-character-memory
       (spg16-shift address index))
      0)
     (spg16-is-uint64-p index)
     (spg16-valid-rw-p
      (spg16-shift address 0)
      (+ 1 index))
     (spg16-string-chars-sint8-through-p
      address index))))

;; Universal closures of A_Strlen.fix_l_strlen and Q_TL_strlen.

(defun-sk spg16-strlen-laws-p ()
  (forall (address)
    (implies
     (spg16-address-p address)
     (and
      (if
          (equal
           (spg16-character-memory
            (spg16-shift address 0))
           0)
          (equal
           (spg16-l-strlen address)
           0)
        (equal
         (spg16-to-uint64
          (+ 1
             (spg16-l-strlen
              (spg16-shift address 1))))
         (spg16-l-strlen address)))
      (spg16-is-uint64-p
       (spg16-l-strlen address))))))

;; Exact unfolding of A_StrSpn.p_in_array. Its witness remains existentially
;; quantified over the full source address type.

(defun-sk spg16-in-array-p (start value)
  (exists (candidate)
    (and
     (spg16-address-p candidate)
     (equal
      (spg16-character-memory candidate)
      value)
     (spg16-addr-le-p start candidate)
     (spg16-addr-lt-p
      candidate
      (spg16-shift
       start
       (spg16-l-strlen start))))))

;; Exact universal closures of the three A_StrPBrk axioms.

(defun-sk spg16-strpbrk-laws-p ()
  (forall (string accept)
    (implies
     (and
      (spg16-address-p string)
      (spg16-address-p accept))
     (and
      (implies
       (equal
        (spg16-character-memory string)
        0)
       (equal
        (spg16-l-strpbrk string accept)
        (spg16-null-address)))
      (implies
       (and
        (not
         (equal
          (spg16-character-memory string)
          0))
        (spg16-in-array-p
         accept
         (spg16-character-memory string)))
       (equal
        (spg16-l-strpbrk string accept)
        string))
      (implies
       (and
        (not
         (equal
          (spg16-character-memory string)
          0))
        (not
         (spg16-in-array-p
          accept
          (spg16-character-memory string))))
       (equal
        (spg16-l-strpbrk
         (spg16-shift string 1)
         accept)
        (spg16-l-strpbrk string accept)))))))

;; The source's three quantified no-match hypotheses remain universal over
;; every address rather than being replaced by external witnesses.

(defun-sk spg16-no-x-before-current-p
    (start current value)
  (forall (candidate)
    (implies
     (spg16-address-p candidate)
     (implies
      (spg16-addr-lt-p candidate current)
      (implies
       (spg16-addr-le-p start candidate)
       (not
        (equal
         value
         (spg16-character-memory candidate))))))))

(defun-sk spg16-no-x-before-end-p
    (start end value)
  (forall (candidate)
    (implies
     (spg16-address-p candidate)
     (implies
      (spg16-addr-le-p start candidate)
      (implies
       (spg16-addr-lt-p candidate end)
       (not
        (equal
         value
         (spg16-character-memory candidate))))))))

(defun-sk spg16-cross-values-distinct-p
    (second-start first-start first-current second-end)
  (forall (first-candidate second-candidate)
    (implies
     (and
      (spg16-address-p first-candidate)
      (spg16-address-p second-candidate))
     (implies
      (spg16-addr-lt-p first-candidate first-current)
      (implies
       (spg16-addr-le-p second-start second-candidate)
       (implies
        (spg16-addr-le-p
         first-start
         first-candidate)
        (implies
         (spg16-addr-lt-p second-candidate second-end)
         (not
          (equal
           (spg16-character-memory first-candidate)
           (spg16-character-memory second-candidate))))))))))

(defun-sk ntp4vc-strpbrk-assert-4-goal16-statement ()
  (forall
   (a1 a2 a a3 a4 a5)
   (implies
    (and
     (spg16-address-p a1)
     (spg16-address-p a2)
     (spg16-address-p a)
     (spg16-address-p a3)
     (spg16-address-p a4)
     (spg16-address-p a5)
     (spg16-function-types-p)
     (spg16-address-order-laws-p)
     (spg16-to-uint64-laws-p)
     (spg16-strlen-laws-p)
     (spg16-strpbrk-laws-p))
    (let*
        ((x
          (spg16-character-memory a1))
         (a6
          (spg16-shift
           a2
           (spg16-l-strlen a2))))
      (implies
       (and
        (equal
         (spg16-character-memory a)
         0)
        (not
         (equal x 0))
        (equal
         (spg16-l-strpbrk a3 a2)
         (spg16-l-strpbrk a1 a2))
        (<=
         (spg16-region
          (spg16-address-base a2))
         0)
        (<=
         (spg16-region
          (spg16-address-base a3))
         0)
        (spg16-linked-p)
        (spg16-sconst-p)
        (spg16-addr-le-p a2 a)
        (spg16-addr-le-p a2 a4)
        (spg16-addr-le-p a3 a1)
        (spg16-addr-le-p a3 a5)
        (spg16-addr-le-p a5 a1)
        (spg16-is-sint8-p x)
        (spg16-valid-string-p a)
        (spg16-valid-string-p a1)
        (spg16-valid-string-p a2)
        (spg16-valid-string-p a3)
        (spg16-addr-lt-p a4 a6)
        (spg16-addr-le-p a a6)
        (spg16-addr-le-p
         a1
         (spg16-shift
          a3
          (spg16-l-strlen a3)))
        (implies
         (spg16-in-array-p a2 x)
         (spg16-in-array-p a x))
        (spg16-no-x-before-current-p
         a2 a x)
        (spg16-no-x-before-end-p
         a2 a6 x)
        (spg16-cross-values-distinct-p
         a2 a3 a1 a6))
       (not
        (equal
         (spg16-character-memory a5)
         (spg16-character-memory a4))))))))

(value-triple :itpeval-statement-checked)

:q
