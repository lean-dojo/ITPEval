;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/verker/strspn_Why3_ide_VCstrspn_assert_2_goal19:
;; the current nonzero signed byte occurs in the accept string under the
;; stated strspn equality, address-order, valid-string, membership-transfer,
;; linkedness, constancy, and quantified prefix-witness hypotheses.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun spnag19-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun spnag19-address-base (address)
  (car address))

(defun spnag19-address-offset (address)
  (cdr address))

(defun spnag19-shift (address amount)
  (cons
   (spnag19-address-base address)
   (+ (spnag19-address-offset address)
      amount)))

;; Conservative interfaces represent the universally arbitrary character
;; memory t_1 and allocation map t, together with the source's region,
;; address-order, logical strlen, logical strspn, unsigned conversion,
;; linkedness, and constancy symbols.

(defstub spnag19-character-memory (address) t)
(defstub spnag19-allocation (index) t)
(defstub spnag19-region (base) t)
(defstub spnag19-addr-le-op (left right) t)
(defstub spnag19-addr-lt-op (left right) t)
(defstub spnag19-l-strlen (address) t)
(defstub spnag19-l-strspn (string accept) t)
(defstub spnag19-to-uint64 (value) t)
(defstub spnag19-linked-op () t)
(defstub spnag19-sconst-op () t)

;; Preserve the source function types over the full address and unbounded
;; mathematical-integer domains.

(defun-sk spnag19-function-types-p ()
  (forall (address other index base value)
    (and
     (implies
      (spnag19-address-p address)
      (and
       (integerp
        (spnag19-character-memory address))
       (integerp
        (spnag19-l-strlen address))))
     (implies
      (and
       (spnag19-address-p address)
       (spnag19-address-p other))
      (integerp
       (spnag19-l-strspn address other)))
     (implies
      (integerp index)
      (integerp
       (spnag19-allocation index)))
     (implies
      (integerp base)
      (integerp
       (spnag19-region base)))
     (implies
      (integerp value)
      (integerp
       (spnag19-to-uint64 value))))))

(defun spnag19-addr-le-p (left right)
  (if (spnag19-addr-le-op left right) t nil))

(defun spnag19-addr-lt-p (left right)
  (if (spnag19-addr-lt-op left right) t nil))

;; On addresses with equal bases, the source address relations are exactly
;; mathematical-integer order on offsets.

(defun-sk spnag19-address-order-laws-p ()
  (forall (left right)
    (implies
     (and
      (spnag19-address-p left)
      (spnag19-address-p right)
      (equal
       (spnag19-address-base left)
       (spnag19-address-base right)))
     (and
      (equal
       (spnag19-addr-le-p left right)
       (<=
        (spnag19-address-offset left)
        (spnag19-address-offset right)))
      (equal
       (spnag19-addr-lt-p left right)
       (<
        (spnag19-address-offset left)
        (spnag19-address-offset right)))))))

(defun spnag19-linked-p ()
  (if (spnag19-linked-op) t nil))

(defun spnag19-sconst-p ()
  (if (spnag19-sconst-op) t nil))

;; Exact mathematical ranges for the source C integer predicates.

(defun spnag19-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun spnag19-is-uint64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; Universal range, identity-on-range, and projection laws for the source's
;; abstract Cint.to_uint64 operation used by logical strlen.

(defun-sk spnag19-to-uint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (spnag19-is-uint64-p
       (spnag19-to-uint64 value))
      (implies
       (spnag19-is-uint64-p value)
       (equal
        (spnag19-to-uint64 value)
        value))
      (equal
       (spnag19-to-uint64
        (spnag19-to-uint64 value))
       (spnag19-to-uint64 value))))))

;; Exact unfolding of Memory.valid_rw for the arbitrary allocation map t.

(defun spnag19-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0
       (spnag19-address-base address))
    (<= 0
        (spnag19-address-offset address))
    (<=
     (+ (spnag19-address-offset address)
        length)
     (spnag19-allocation
      (spnag19-address-base address))))))

;; Exact unfolding of A_Strlen.p_valid_str. The terminating position remains
;; an internal existential over all mathematical integers, and its character
;; range condition remains universally quantified over all integers.

(defun-sk spnag19-string-chars-sint8-through-p
    (address bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position bound)
      (spnag19-is-sint8-p
       (spnag19-character-memory
        (spnag19-shift address position)))))))

(defun-sk spnag19-valid-string-p (address)
  (exists (index)
    (and
     (integerp index)
     (equal
      (spnag19-character-memory
       (spnag19-shift address index))
      0)
     (spnag19-is-uint64-p index)
     (spnag19-valid-rw-p
      (spnag19-shift address 0)
      (+ 1 index))
     (spnag19-string-chars-sint8-through-p
      address index))))

;; Universal closures of A_Strlen.fix_l_strlen and Q_TL_strlen.

(defun-sk spnag19-strlen-laws-p ()
  (forall (address)
    (implies
     (spnag19-address-p address)
     (and
      (if
          (equal
           (spnag19-character-memory
            (spnag19-shift address 0))
           0)
          (equal
           (spnag19-l-strlen address)
           0)
        (equal
         (spnag19-to-uint64
          (+ 1
             (spnag19-l-strlen
              (spnag19-shift address 1))))
         (spnag19-l-strlen address)))
      (spnag19-is-uint64-p
       (spnag19-l-strlen address))))))

;; Exact unfolding of A_StrSpn.p_in_array. Its witness remains existentially
;; quantified over the full source address type.

(defun-sk spnag19-in-array-p (start value)
  (exists (candidate)
    (and
     (spnag19-address-p candidate)
     (equal
      (spnag19-character-memory candidate)
      value)
     (spnag19-addr-le-p start candidate)
     (spnag19-addr-lt-p
      candidate
      (spnag19-shift
       start
       (spnag19-l-strlen start))))))

;; Exact universal closures of the three A_StrSpn axioms.

(defun-sk spnag19-strspn-laws-p ()
  (forall (string accept)
    (implies
     (and
      (spnag19-address-p string)
      (spnag19-address-p accept))
     (and
      (implies
       (equal
        (spnag19-character-memory string)
        0)
       (equal
        (spnag19-l-strspn string accept)
        0))
      (implies
       (and
        (not
         (equal
          (spnag19-character-memory string)
          0))
        (not
         (spnag19-in-array-p
          accept
          (spnag19-character-memory string))))
       (equal
        (spnag19-l-strspn string accept)
        0))
      (implies
       (and
        (not
         (equal
          (spnag19-character-memory string)
          0))
        (spnag19-in-array-p
         accept
         (spnag19-character-memory string)))
       (equal
        (+ 1
           (spnag19-l-strspn
            (spnag19-shift string 1)
            accept))
        (spnag19-l-strspn string accept)))))))

;; The source's no-match hypothesis remains universal over every address.

(defun-sk spnag19-no-match-before-p
    (start current value)
  (forall (candidate)
    (implies
     (spnag19-address-p candidate)
     (implies
      (spnag19-addr-lt-p candidate current)
      (implies
       (spnag19-addr-le-p start candidate)
       (not
        (equal
         value
         (spnag19-character-memory candidate))))))))

;; For each source-prefix address, the matching accept-string address remains
;; an internal existential over the full address type.

(defun-sk spnag19-accept-witness-p
    (source-candidate accept-start accept-end)
  (exists (accept-candidate)
    (and
     (spnag19-address-p accept-candidate)
     (equal
      (spnag19-character-memory source-candidate)
      (spnag19-character-memory accept-candidate))
     (spnag19-addr-le-p
      accept-start
      accept-candidate)
     (spnag19-addr-lt-p
      accept-candidate
      accept-end))))

(defun-sk spnag19-prefix-values-in-accept-p
    (source-start source-current accept-start accept-end)
  (forall (source-candidate)
    (implies
     (spnag19-address-p source-candidate)
     (implies
      (spnag19-addr-lt-p
       source-candidate
       source-current)
      (implies
       (spnag19-addr-le-p
        source-start
        source-candidate)
       (spnag19-accept-witness-p
        source-candidate
        accept-start
        accept-end))))))

(defun-sk ntp4vc-strspn-assert-2-goal19-statement ()
  (forall
   (a1 a3 a a2)
   (implies
    (and
     (spnag19-address-p a1)
     (spnag19-address-p a3)
     (spnag19-address-p a)
     (spnag19-address-p a2)
     (spnag19-function-types-p)
     (spnag19-address-order-laws-p)
     (spnag19-to-uint64-laws-p)
     (spnag19-strlen-laws-p)
     (spnag19-strspn-laws-p))
    (let*
        ((x
          (spnag19-character-memory a1))
         (x1
          (spnag19-character-memory a3))
         (x2
          (spnag19-address-offset a1))
         (x3
          (spnag19-address-offset a))
         (x4
          (spnag19-l-strlen a))
         (a4
          (spnag19-shift
           a2
           (spnag19-l-strlen a2))))
      (implies
       (and
        (not (equal x 0))
        (not (equal x1 0))
        (equal x1 x)
        (equal
         (+ x2
            (spnag19-l-strspn a1 a2))
         (+ x3
            (spnag19-l-strspn a a2)))
        (<= x3 x2)
        (<=
         (spnag19-region
          (spnag19-address-base a))
         0)
        (<=
         (spnag19-region
          (spnag19-address-base a2))
         0)
        (<= x2 (+ x3 x4))
        (spnag19-linked-p)
        (spnag19-sconst-p)
        (spnag19-addr-le-p a a1)
        (spnag19-addr-le-p a2 a3)
        (spnag19-is-sint8-p x)
        (spnag19-is-sint8-p x1)
        (spnag19-valid-string-p a)
        (spnag19-valid-string-p a1)
        (spnag19-valid-string-p a2)
        (spnag19-valid-string-p a3)
        (spnag19-is-uint64-p (- x2 x3))
        (spnag19-addr-le-p
         a1
         (spnag19-shift a x4))
        (spnag19-addr-le-p a3 a4)
        (implies
         (spnag19-in-array-p a2 x)
         (spnag19-in-array-p a3 x))
        (spnag19-no-match-before-p
         a2 a3 x)
        (spnag19-prefix-values-in-accept-p
         a a1 a2 a4))
       (spnag19-in-array-p a2 x))))))

(value-triple :itpeval-statement-checked)

:q
