;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/verker/strspn_Why3_ide_VCstrspn_loop_term_2_positive_goal20:
;; the current accept-string offset is at most its start offset plus its
;; logical length, under the stated strspn, address-order, valid-string,
;; membership-transfer, and quantified range hypotheses.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun spg20-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun spg20-address-base (address)
  (car address))

(defun spg20-address-offset (address)
  (cdr address))

(defun spg20-shift (address amount)
  (cons
   (spg20-address-base address)
   (+ (spg20-address-offset address)
      amount)))

;; Conservative interfaces represent the universally arbitrary character
;; memory t_1 and allocation map t, together with the source's region,
;; address-order, logical strlen, logical strspn, unsigned conversion,
;; linkedness, and constancy symbols.

(defstub spg20-character-memory (address) t)
(defstub spg20-allocation (index) t)
(defstub spg20-region (base) t)
(defstub spg20-addr-le-op (left right) t)
(defstub spg20-addr-lt-op (left right) t)
(defstub spg20-l-strlen (address) t)
(defstub spg20-l-strspn (string accept) t)
(defstub spg20-to-uint64 (value) t)
(defstub spg20-linked-op () t)
(defstub spg20-sconst-op () t)

;; Preserve the source function types over the full address and unbounded
;; mathematical-integer domains.

(defun-sk spg20-function-types-p ()
  (forall (address other index base value)
    (and
     (implies
      (spg20-address-p address)
      (and
       (integerp
        (spg20-character-memory address))
       (integerp
        (spg20-l-strlen address))))
     (implies
      (and
       (spg20-address-p address)
       (spg20-address-p other))
      (integerp
       (spg20-l-strspn address other)))
     (implies
      (integerp index)
      (integerp
       (spg20-allocation index)))
     (implies
      (integerp base)
      (integerp
       (spg20-region base)))
     (implies
      (integerp value)
      (integerp
       (spg20-to-uint64 value))))))

(defun spg20-addr-le-p (left right)
  (if (spg20-addr-le-op left right) t nil))

(defun spg20-addr-lt-p (left right)
  (if (spg20-addr-lt-op left right) t nil))

;; On addresses with equal bases, the source address relations are exactly
;; mathematical-integer order on offsets.

(defun-sk spg20-address-order-laws-p ()
  (forall (left right)
    (implies
     (and
      (spg20-address-p left)
      (spg20-address-p right)
      (equal
       (spg20-address-base left)
       (spg20-address-base right)))
     (and
      (equal
       (spg20-addr-le-p left right)
       (<=
        (spg20-address-offset left)
        (spg20-address-offset right)))
      (equal
       (spg20-addr-lt-p left right)
       (<
        (spg20-address-offset left)
        (spg20-address-offset right)))))))

(defun spg20-linked-p ()
  (if (spg20-linked-op) t nil))

(defun spg20-sconst-p ()
  (if (spg20-sconst-op) t nil))

;; Exact mathematical ranges for the source C integer predicates.

(defun spg20-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun spg20-is-uint64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; Universal range, identity-on-range, and idempotence laws for the source's
;; abstract Cint.to_uint64 operation used by logical strlen.

(defun-sk spg20-to-uint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (spg20-is-uint64-p
       (spg20-to-uint64 value))
      (implies
       (spg20-is-uint64-p value)
       (equal
        (spg20-to-uint64 value)
        value))
      (equal
       (spg20-to-uint64
        (spg20-to-uint64 value))
       (spg20-to-uint64 value))))))

;; Exact unfolding of Memory.valid_rw for the arbitrary allocation map t.

(defun spg20-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0
       (spg20-address-base address))
    (<= 0
        (spg20-address-offset address))
    (<=
     (+ (spg20-address-offset address)
        length)
     (spg20-allocation
      (spg20-address-base address))))))

;; Exact unfolding of A_Strlen.p_valid_str. The terminating position remains
;; an internal existential over all mathematical integers, and its character
;; range condition remains universally quantified over all integers.

(defun-sk spg20-string-chars-sint8-through-p
    (address bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position bound)
      (spg20-is-sint8-p
       (spg20-character-memory
        (spg20-shift address position)))))))

(defun-sk spg20-valid-string-p (address)
  (exists (index)
    (and
     (integerp index)
     (equal
      (spg20-character-memory
       (spg20-shift address index))
      0)
     (spg20-is-uint64-p index)
     (spg20-valid-rw-p
      (spg20-shift address 0)
      (+ 1 index))
     (spg20-string-chars-sint8-through-p
      address index))))

;; Universal closures of A_Strlen.fix_l_strlen and Q_TL_strlen.

(defun-sk spg20-strlen-laws-p ()
  (forall (address)
    (implies
     (spg20-address-p address)
     (and
      (if
          (equal
           (spg20-character-memory
            (spg20-shift address 0))
           0)
          (equal
           (spg20-l-strlen address)
           0)
        (equal
         (spg20-to-uint64
          (+ 1
             (spg20-l-strlen
              (spg20-shift address 1))))
         (spg20-l-strlen address)))
      (spg20-is-uint64-p
       (spg20-l-strlen address))))))

;; Exact unfolding of A_StrSpn.p_in_array. Its witness remains existentially
;; quantified over the full source address type.

(defun-sk spg20-in-array-p (start value)
  (exists (candidate)
    (and
     (spg20-address-p candidate)
     (equal
      (spg20-character-memory candidate)
      value)
     (spg20-addr-le-p start candidate)
     (spg20-addr-lt-p
      candidate
      (spg20-shift
       start
       (spg20-l-strlen start))))))

;; Exact universal closures of the three A_StrSpn axioms.

(defun-sk spg20-strspn-laws-p ()
  (forall (string accept)
    (implies
     (and
      (spg20-address-p string)
      (spg20-address-p accept))
     (and
      (implies
       (equal
        (spg20-character-memory string)
        0)
       (equal
        (spg20-l-strspn string accept)
        0))
      (implies
       (and
        (not
         (equal
          (spg20-character-memory string)
          0))
        (not
         (spg20-in-array-p
          accept
          (spg20-character-memory string))))
       (equal
        (spg20-l-strspn string accept)
        0))
      (implies
       (and
        (not
         (equal
          (spg20-character-memory string)
          0))
        (spg20-in-array-p
         accept
         (spg20-character-memory string)))
       (equal
        (+ 1
           (spg20-l-strspn
            (spg20-shift string 1)
            accept))
        (spg20-l-strspn string accept)))))))

;; The source's no-match hypothesis remains universal over every address.

(defun-sk spg20-no-match-before-p
    (start current value)
  (forall (candidate)
    (implies
     (spg20-address-p candidate)
     (implies
      (spg20-addr-lt-p candidate current)
      (implies
       (spg20-addr-le-p start candidate)
       (not
        (equal
         value
         (spg20-character-memory candidate))))))))

;; For each source-prefix address, the matching accept-string address remains
;; an internal existential over the full address type.

(defun-sk spg20-accept-witness-p
    (source-candidate accept-start accept-end)
  (exists (accept-candidate)
    (and
     (spg20-address-p accept-candidate)
     (equal
      (spg20-character-memory source-candidate)
      (spg20-character-memory accept-candidate))
     (spg20-addr-le-p
      accept-start
      accept-candidate)
     (spg20-addr-lt-p
      accept-candidate
      accept-end))))

(defun-sk spg20-prefix-values-in-accept-p
    (source-start source-current accept-start accept-end)
  (forall (source-candidate)
    (implies
     (spg20-address-p source-candidate)
     (implies
      (spg20-addr-lt-p
       source-candidate
       source-current)
      (implies
       (spg20-addr-le-p
        source-start
        source-candidate)
       (spg20-accept-witness-p
        source-candidate
        accept-start
        accept-end))))))

(defun-sk
    ntp4vc-strspn-loop-term-2-positive-goal20-statement ()
  (forall
   (a1 a3 a a2)
   (implies
    (and
     (spg20-address-p a1)
     (spg20-address-p a3)
     (spg20-address-p a)
     (spg20-address-p a2)
     (spg20-function-types-p)
     (spg20-address-order-laws-p)
     (spg20-to-uint64-laws-p)
     (spg20-strlen-laws-p)
     (spg20-strspn-laws-p))
    (let*
        ((x
          (spg20-character-memory a1))
         (x1
          (spg20-character-memory a3))
         (x2
          (spg20-address-offset a1))
         (x3
          (spg20-address-offset a))
         (x4
          (spg20-l-strlen a))
         (x5
          (spg20-l-strlen a2))
         (a4
          (spg20-shift a2 x5)))
      (implies
       (and
        (not (equal x 0))
        (not (equal x1 0))
        (not (equal x1 x))
        (equal
         (+ x2
            (spg20-l-strspn a1 a2))
         (+ x3
            (spg20-l-strspn a a2)))
        (<= x3 x2)
        (<=
         (spg20-region
          (spg20-address-base a))
         0)
        (<=
         (spg20-region
          (spg20-address-base a2))
         0)
        (<= x2 (+ x3 x4))
        (spg20-linked-p)
        (spg20-sconst-p)
        (spg20-addr-le-p a a1)
        (spg20-addr-le-p a2 a3)
        (spg20-is-sint8-p x)
        (spg20-is-sint8-p x1)
        (spg20-valid-string-p a)
        (spg20-valid-string-p a1)
        (spg20-valid-string-p a2)
        (spg20-valid-string-p a3)
        (spg20-is-uint64-p (- x2 x3))
        (spg20-addr-le-p
         a1
         (spg20-shift a x4))
        (spg20-addr-le-p a3 a4)
        (implies
         (spg20-in-array-p a2 x)
         (spg20-in-array-p a3 x))
        (spg20-no-match-before-p
         a2 a3 x)
        (spg20-prefix-values-in-accept-p
         a a1 a2 a4))
       (<=
        (spg20-address-offset a3)
        (+ (spg20-address-offset a2)
           x5)))))))

(value-triple :itpeval-statement-checked)

:q
