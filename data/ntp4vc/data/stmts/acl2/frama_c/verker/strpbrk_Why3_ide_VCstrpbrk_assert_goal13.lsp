;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/verker/strpbrk_Why3_ide_VCstrpbrk_assert_goal13:
;; both current positions lie strictly before their respective string ends
;; under the stated strpbrk equality, valid-string, address-order, membership,
;; and quantified no-match hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun spg13-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun spg13-address-base (address)
  (car address))

(defun spg13-address-offset (address)
  (cdr address))

(defun spg13-shift (address amount)
  (cons
   (spg13-address-base address)
   (+ (spg13-address-offset address)
      amount)))

(defun spg13-null-address ()
  (cons 0 0))

;; Conservative interfaces represent the universally arbitrary character
;; memory t_1 and allocation map t, together with the source's region,
;; address-order, logical strlen, logical strpbrk, unsigned conversion,
;; linkedness, and constancy symbols.

(defstub spg13-character-memory (address) t)
(defstub spg13-allocation (index) t)
(defstub spg13-region (base) t)
(defstub spg13-addr-le-op (left right) t)
(defstub spg13-addr-lt-op (left right) t)
(defstub spg13-l-strlen (address) t)
(defstub spg13-l-strpbrk (string accept) t)
(defstub spg13-to-uint64 (value) t)
(defstub spg13-linked-op () t)
(defstub spg13-sconst-op () t)

;; Preserve the source function types over the full address and unbounded
;; mathematical-integer domains.

(defun-sk spg13-function-types-p ()
  (forall (address other index base value)
    (and
     (implies
      (spg13-address-p address)
      (and
       (integerp
        (spg13-character-memory address))
       (integerp
        (spg13-l-strlen address))))
     (implies
      (and
       (spg13-address-p address)
       (spg13-address-p other))
      (spg13-address-p
       (spg13-l-strpbrk address other)))
     (implies
      (integerp index)
      (integerp
       (spg13-allocation index)))
     (implies
      (integerp base)
      (integerp
       (spg13-region base)))
     (implies
      (integerp value)
      (integerp
       (spg13-to-uint64 value))))))

(defun spg13-addr-le-p (left right)
  (if (spg13-addr-le-op left right) t nil))

(defun spg13-addr-lt-p (left right)
  (if (spg13-addr-lt-op left right) t nil))

;; On addresses with equal bases, the source address relations are exactly
;; mathematical-integer order on offsets.

(defun-sk spg13-address-order-laws-p ()
  (forall (left right)
    (implies
     (and
      (spg13-address-p left)
      (spg13-address-p right)
      (equal
       (spg13-address-base left)
       (spg13-address-base right)))
     (and
      (equal
       (spg13-addr-le-p left right)
       (<=
        (spg13-address-offset left)
        (spg13-address-offset right)))
      (equal
       (spg13-addr-lt-p left right)
       (<
        (spg13-address-offset left)
        (spg13-address-offset right)))))))

(defun spg13-linked-p ()
  (if (spg13-linked-op) t nil))

(defun spg13-sconst-p ()
  (if (spg13-sconst-op) t nil))

;; Exact mathematical ranges for the source C integer predicates.

(defun spg13-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun spg13-is-uint64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; Universal range, identity-on-range, and projection laws for the source's
;; abstract Cint.to_uint64 operation used by logical strlen.

(defun-sk spg13-to-uint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (spg13-is-uint64-p
       (spg13-to-uint64 value))
      (implies
       (spg13-is-uint64-p value)
       (equal
        (spg13-to-uint64 value)
        value))
      (equal
       (spg13-to-uint64
        (spg13-to-uint64 value))
       (spg13-to-uint64 value))))))

;; Exact unfolding of Memory.valid_rw for the arbitrary allocation map t.

(defun spg13-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0
       (spg13-address-base address))
    (<= 0
        (spg13-address-offset address))
    (<=
     (+ (spg13-address-offset address)
        length)
     (spg13-allocation
      (spg13-address-base address))))))

;; Exact unfolding of A_Strlen.p_valid_str. The terminating position remains
;; an internal existential over all mathematical integers, and its character
;; range condition remains universally quantified over all integers.

(defun-sk spg13-string-chars-sint8-through-p
    (address bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position bound)
      (spg13-is-sint8-p
       (spg13-character-memory
        (spg13-shift address position)))))))

(defun-sk spg13-valid-string-p (address)
  (exists (index)
    (and
     (integerp index)
     (equal
      (spg13-character-memory
       (spg13-shift address index))
      0)
     (spg13-is-uint64-p index)
     (spg13-valid-rw-p
      (spg13-shift address 0)
      (+ 1 index))
     (spg13-string-chars-sint8-through-p
      address index))))

;; Universal closures of A_Strlen.fix_l_strlen and Q_TL_strlen.

(defun-sk spg13-strlen-laws-p ()
  (forall (address)
    (implies
     (spg13-address-p address)
     (and
      (if
          (equal
           (spg13-character-memory
            (spg13-shift address 0))
           0)
          (equal
           (spg13-l-strlen address)
           0)
        (equal
         (spg13-to-uint64
          (+ 1
             (spg13-l-strlen
              (spg13-shift address 1))))
         (spg13-l-strlen address)))
      (spg13-is-uint64-p
       (spg13-l-strlen address))))))

;; Exact unfolding of A_StrSpn.p_in_array. Its witness remains existentially
;; quantified over the full source address type.

(defun-sk spg13-in-array-p (start value)
  (exists (candidate)
    (and
     (spg13-address-p candidate)
     (equal
      (spg13-character-memory candidate)
      value)
     (spg13-addr-le-p start candidate)
     (spg13-addr-lt-p
      candidate
      (spg13-shift
       start
       (spg13-l-strlen start))))))

;; Exact universal closures of the three A_StrPBrk axioms.

(defun-sk spg13-strpbrk-laws-p ()
  (forall (string accept)
    (implies
     (and
      (spg13-address-p string)
      (spg13-address-p accept))
     (and
      (implies
       (equal
        (spg13-character-memory string)
        0)
       (equal
        (spg13-l-strpbrk string accept)
        (spg13-null-address)))
      (implies
       (and
        (not
         (equal
          (spg13-character-memory string)
          0))
        (spg13-in-array-p
         accept
         (spg13-character-memory string)))
       (equal
        (spg13-l-strpbrk string accept)
        string))
      (implies
       (and
        (not
         (equal
          (spg13-character-memory string)
          0))
        (not
         (spg13-in-array-p
          accept
          (spg13-character-memory string))))
       (equal
        (spg13-l-strpbrk
         (spg13-shift string 1)
         accept)
        (spg13-l-strpbrk string accept)))))))

;; The source's quantified no-match hypotheses remain universal over every
;; address rather than being replaced by external witnesses.

(defun-sk spg13-no-x-before-current-p
    (start current value)
  (forall (candidate)
    (implies
     (spg13-address-p candidate)
     (implies
      (spg13-addr-lt-p candidate current)
      (implies
       (spg13-addr-le-p start candidate)
       (not
        (equal
         value
         (spg13-character-memory candidate))))))))

(defun-sk spg13-cross-values-distinct-p
    (second-start first-start first-current second-end)
  (forall (first-candidate second-candidate)
    (implies
     (and
      (spg13-address-p first-candidate)
      (spg13-address-p second-candidate))
     (implies
      (spg13-addr-lt-p first-candidate first-current)
      (implies
       (spg13-addr-le-p second-start second-candidate)
       (implies
        (spg13-addr-le-p first-start first-candidate)
        (implies
         (spg13-addr-lt-p second-candidate second-end)
         (not
          (equal
           (spg13-character-memory first-candidate)
           (spg13-character-memory second-candidate))))))))))

(defun-sk ntp4vc-strpbrk-assert-goal13-statement ()
  (forall
   (a a1 a2 a3)
   (implies
    (and
     (spg13-address-p a)
     (spg13-address-p a1)
     (spg13-address-p a2)
     (spg13-address-p a3)
     (spg13-function-types-p)
     (spg13-address-order-laws-p)
     (spg13-to-uint64-laws-p)
     (spg13-strlen-laws-p)
     (spg13-strpbrk-laws-p))
    (let*
        ((x
          (spg13-character-memory a))
         (x1
          (spg13-character-memory a1))
         (a4
          (spg13-shift
           a2
           (spg13-l-strlen a2)))
         (a5
          (spg13-shift
           a3
           (spg13-l-strlen a3))))
      (implies
       (and
        (not (equal x 0))
        (not (equal x1 0))
        (equal x1 x)
        (equal
         (spg13-l-strpbrk a3 a2)
         (spg13-l-strpbrk a1 a2))
        (<=
         (spg13-region
          (spg13-address-base a2))
         0)
        (<=
         (spg13-region
          (spg13-address-base a3))
         0)
        (spg13-linked-p)
        (spg13-sconst-p)
        (spg13-addr-le-p a2 a)
        (spg13-addr-le-p a3 a1)
        (spg13-is-sint8-p x)
        (spg13-is-sint8-p x1)
        (spg13-valid-string-p a)
        (spg13-valid-string-p a1)
        (spg13-valid-string-p a2)
        (spg13-valid-string-p a3)
        (spg13-addr-le-p a a4)
        (spg13-addr-le-p a1 a5)
        (implies
         (spg13-in-array-p a2 x1)
         (spg13-in-array-p a x1))
        (spg13-no-x-before-current-p
         a2 a x1)
        (spg13-cross-values-distinct-p
         a2 a3 a1 a4))
       (and
        (spg13-addr-lt-p a a4)
        (spg13-addr-lt-p a1 a5)))))))

(value-triple :itpeval-statement-checked)

:q
