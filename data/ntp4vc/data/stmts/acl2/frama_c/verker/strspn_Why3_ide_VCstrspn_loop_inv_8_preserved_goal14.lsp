;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/verker/strspn_Why3_ide_VCstrspn_loop_inv_8_preserved_goal14:
;; preservation of the strspn loop invariant that the byte at a constrained
;; accept-region address differs from the current source byte, under the stated
;; string, address-order, membership-transfer, and quantified prefix hypotheses.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun spg14-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun spg14-address-base (address)
  (car address))

(defun spg14-address-offset (address)
  (cdr address))

(defun spg14-shift (address amount)
  (cons
   (spg14-address-base address)
   (+ (spg14-address-offset address)
      amount)))

;; Conservative interfaces represent the universally arbitrary character
;; memory t_1 and allocation map t, together with the source's region,
;; address-order, logical strlen, logical strspn, unsigned conversion,
;; linkedness, and constancy symbols.

(defstub spg14-character-memory (address) t)
(defstub spg14-allocation (index) t)
(defstub spg14-region (base) t)
(defstub spg14-addr-le-op (left right) t)
(defstub spg14-addr-lt-op (left right) t)
(defstub spg14-l-strlen (address) t)
(defstub spg14-l-strspn (string accept) t)
(defstub spg14-to-uint64 (value) t)
(defstub spg14-to-sint64 (value) t)
(defstub spg14-linked-op () t)
(defstub spg14-sconst-op () t)

;; Preserve the source function types over the full address and unbounded
;; mathematical-integer domains.

(defun-sk spg14-function-types-p ()
  (forall (address other index base value)
    (and
     (implies
      (spg14-address-p address)
      (and
       (integerp
        (spg14-character-memory address))
       (integerp
        (spg14-l-strlen address))))
     (implies
      (and
       (spg14-address-p address)
       (spg14-address-p other))
      (integerp
       (spg14-l-strspn address other)))
     (implies
      (integerp index)
      (integerp
       (spg14-allocation index)))
     (implies
      (integerp base)
      (integerp
       (spg14-region base)))
     (implies
      (integerp value)
      (and
       (integerp
        (spg14-to-uint64 value))
       (integerp
        (spg14-to-sint64 value)))))))

(defun spg14-addr-le-p (left right)
  (if (spg14-addr-le-op left right) t nil))

(defun spg14-addr-lt-p (left right)
  (if (spg14-addr-lt-op left right) t nil))

;; On addresses with equal bases, the source address relations are exactly
;; mathematical-integer order on offsets.

(defun-sk spg14-address-order-laws-p ()
  (forall (left right)
    (implies
     (and
      (spg14-address-p left)
      (spg14-address-p right)
      (equal
       (spg14-address-base left)
       (spg14-address-base right)))
     (and
      (equal
       (spg14-addr-le-p left right)
       (<=
        (spg14-address-offset left)
        (spg14-address-offset right)))
      (equal
       (spg14-addr-lt-p left right)
       (<
        (spg14-address-offset left)
        (spg14-address-offset right)))))))

(defun spg14-linked-p ()
  (if (spg14-linked-op) t nil))

(defun spg14-sconst-p ()
  (if (spg14-sconst-op) t nil))

;; Exact mathematical ranges for the source C integer predicates.

(defun spg14-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun spg14-is-uint64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

(defun spg14-is-sint64-p (value)
  (and
   (integerp value)
   (<= -9223372036854775808 value)
   (< value 9223372036854775808)))

;; Universal range, identity-on-range, and idempotence laws for the source's
;; abstract Cint.to_uint64 and Cint.to_sint64 operations.

(defun-sk spg14-to-uint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (spg14-is-uint64-p
       (spg14-to-uint64 value))
      (implies
       (spg14-is-uint64-p value)
       (equal
        (spg14-to-uint64 value)
        value))
      (equal
       (spg14-to-uint64
        (spg14-to-uint64 value))
       (spg14-to-uint64 value))))))

(defun-sk spg14-to-sint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (spg14-is-sint64-p
       (spg14-to-sint64 value))
      (implies
       (spg14-is-sint64-p value)
       (equal
        (spg14-to-sint64 value)
        value))
      (equal
       (spg14-to-sint64
        (spg14-to-sint64 value))
       (spg14-to-sint64 value))))))

;; Exact universal closure of Cint.proj_int64.

(defun-sk spg14-proj-int64-law-p ()
  (forall (value)
    (implies
     (integerp value)
     (equal
      (spg14-to-sint64
       (spg14-to-uint64 value))
      (spg14-to-sint64 value)))))

;; Exact unfolding of Memory.valid_rw for the arbitrary allocation map t.

(defun spg14-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0
       (spg14-address-base address))
    (<= 0
        (spg14-address-offset address))
    (<=
     (+ (spg14-address-offset address)
        length)
     (spg14-allocation
      (spg14-address-base address))))))

;; Exact unfolding of A_Strlen.p_valid_str. The terminating position remains
;; an internal existential over all mathematical integers, and its character
;; range condition remains universally quantified over all integers.

(defun-sk spg14-string-chars-sint8-through-p
    (address bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position bound)
      (spg14-is-sint8-p
       (spg14-character-memory
        (spg14-shift address position)))))))

(defun-sk spg14-valid-string-p (address)
  (exists (index)
    (and
     (integerp index)
     (equal
      (spg14-character-memory
       (spg14-shift address index))
      0)
     (spg14-is-uint64-p index)
     (spg14-valid-rw-p
      (spg14-shift address 0)
      (+ 1 index))
     (spg14-string-chars-sint8-through-p
      address index))))

;; Universal closures of A_Strlen.fix_l_strlen and Q_TL_strlen.

(defun-sk spg14-strlen-laws-p ()
  (forall (address)
    (implies
     (spg14-address-p address)
     (and
      (if
          (equal
           (spg14-character-memory
            (spg14-shift address 0))
           0)
          (equal
           (spg14-l-strlen address)
           0)
        (equal
         (spg14-to-uint64
          (+ 1
             (spg14-l-strlen
              (spg14-shift address 1))))
         (spg14-l-strlen address)))
      (spg14-is-uint64-p
       (spg14-l-strlen address))))))

;; Exact unfolding of A_StrSpn.p_in_array. Its witness remains existentially
;; quantified over the full source address type.

(defun-sk spg14-in-array-p (start value)
  (exists (candidate)
    (and
     (spg14-address-p candidate)
     (equal
      (spg14-character-memory candidate)
      value)
     (spg14-addr-le-p start candidate)
     (spg14-addr-lt-p
      candidate
      (spg14-shift
       start
       (spg14-l-strlen start))))))

;; Exact universal closures of the three A_StrSpn axioms.

(defun-sk spg14-strspn-laws-p ()
  (forall (string accept)
    (implies
     (and
      (spg14-address-p string)
      (spg14-address-p accept))
     (and
      (implies
       (equal
        (spg14-character-memory string)
        0)
       (equal
        (spg14-l-strspn string accept)
        0))
      (implies
       (and
        (not
         (equal
          (spg14-character-memory string)
          0))
        (not
         (spg14-in-array-p
          accept
          (spg14-character-memory string))))
       (equal
        (spg14-l-strspn string accept)
        0))
      (implies
       (and
        (not
         (equal
          (spg14-character-memory string)
          0))
        (spg14-in-array-p
         accept
         (spg14-character-memory string)))
       (equal
        (+ 1
           (spg14-l-strspn
            (spg14-shift string 1)
            accept))
        (spg14-l-strspn string accept)))))))

;; The source's no-match hypothesis remains universal over every address.

(defun-sk spg14-no-match-before-p
    (start current value)
  (forall (candidate)
    (implies
     (spg14-address-p candidate)
     (implies
      (spg14-addr-lt-p candidate current)
      (implies
       (spg14-addr-le-p start candidate)
       (not
        (equal
         value
         (spg14-character-memory candidate))))))))

;; For each source-prefix address, the matching accept-string address remains
;; an internal existential over the full address type.

(defun-sk spg14-accept-witness-p
    (source-candidate accept-start accept-end)
  (exists (accept-candidate)
    (and
     (spg14-address-p accept-candidate)
     (equal
      (spg14-character-memory source-candidate)
      (spg14-character-memory accept-candidate))
     (spg14-addr-le-p
      accept-start
      accept-candidate)
     (spg14-addr-lt-p
      accept-candidate
      accept-end))))

(defun-sk spg14-prefix-values-in-accept-p
    (source-start source-current accept-start accept-end)
  (forall (source-candidate)
    (implies
     (spg14-address-p source-candidate)
     (implies
      (spg14-addr-lt-p
       source-candidate
       source-current)
      (implies
       (spg14-addr-le-p
        source-start
        source-candidate)
       (spg14-accept-witness-p
        source-candidate
        accept-start
        accept-end))))))

(defun-sk ntp4vc-strspn-loop-inv-8-preserved-goal14-statement ()
  (forall
   (a1 a3 a a2 a4)
   (implies
    (and
     (spg14-address-p a1)
     (spg14-address-p a3)
     (spg14-address-p a)
     (spg14-address-p a2)
     (spg14-address-p a4)
     (spg14-function-types-p)
     (spg14-address-order-laws-p)
     (spg14-to-uint64-laws-p)
     (spg14-to-sint64-laws-p)
     (spg14-proj-int64-law-p)
     (spg14-strlen-laws-p)
     (spg14-strspn-laws-p))
    (let*
        ((x
          (spg14-character-memory a1))
         (x1
          (spg14-character-memory a3))
         (x2
          (spg14-address-offset a1))
         (x3
          (spg14-address-offset a))
         (x4
          (spg14-l-strlen a))
         (a5
          (spg14-shift
           a2
           (spg14-l-strlen a2))))
      (implies
       (and
        (not (equal x 0))
        (not (equal x1 0))
        (not (equal x1 x))
        (equal
         (+ x2
            (spg14-l-strspn a1 a2))
         (+ x3
            (spg14-l-strspn a a2)))
        (<= x3 x2)
        (<=
         (spg14-region
          (spg14-address-base a))
         0)
        (<=
         (spg14-region
          (spg14-address-base a2))
         0)
        (<= x2 (+ x3 x4))
        (spg14-linked-p)
        (spg14-sconst-p)
        (spg14-addr-le-p a a1)
        (spg14-addr-le-p a2 a3)
        (spg14-addr-le-p a2 a4)
        (spg14-is-sint8-p x)
        (spg14-is-sint8-p x1)
        (spg14-valid-string-p a)
        (spg14-valid-string-p a1)
        (spg14-valid-string-p a2)
        (spg14-valid-string-p a3)
        (spg14-addr-lt-p
         a4
         (spg14-shift a3 1))
        (spg14-is-uint64-p (- x2 x3))
        (spg14-addr-le-p
         a1
         (spg14-shift a x4))
        (spg14-addr-le-p a3 a5)
        (implies
         (spg14-in-array-p a2 x)
         (spg14-in-array-p a3 x))
        (spg14-no-match-before-p
         a2 a3 x)
        (spg14-prefix-values-in-accept-p
         a a1 a2 a5))
       (not
        (equal
         (spg14-character-memory a4)
         x)))))))

(value-triple :itpeval-statement-checked)

:q
