;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/verker/strspn_Why3_ide_VCstrspn_loop_inv_7_preserved_goal12:
;; preservation of the strspn loop invariant placing the next accept-string
;; address between the accept start and logical end under the stated string,
;; address-order, membership-transfer, and quantified prefix hypotheses.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun spg12-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun spg12-address-base (address)
  (car address))

(defun spg12-address-offset (address)
  (cdr address))

(defun spg12-shift (address amount)
  (cons
   (spg12-address-base address)
   (+ (spg12-address-offset address)
      amount)))

;; Conservative interfaces represent the universally arbitrary character
;; memory t_1 and allocation map t, together with the source's region,
;; address-order, logical strlen, logical strspn, unsigned conversion,
;; linkedness, and constancy symbols.

(defstub spg12-character-memory (address) t)
(defstub spg12-allocation (index) t)
(defstub spg12-region (base) t)
(defstub spg12-addr-le-op (left right) t)
(defstub spg12-addr-lt-op (left right) t)
(defstub spg12-l-strlen (address) t)
(defstub spg12-l-strspn (string accept) t)
(defstub spg12-to-uint64 (value) t)
(defstub spg12-linked-op () t)
(defstub spg12-sconst-op () t)

;; Preserve the source function types over the full address and unbounded
;; mathematical-integer domains.

(defun-sk spg12-function-types-p ()
  (forall (address other index base value)
    (and
     (implies
      (spg12-address-p address)
      (and
       (integerp
        (spg12-character-memory address))
       (integerp
        (spg12-l-strlen address))))
     (implies
      (and
       (spg12-address-p address)
       (spg12-address-p other))
      (integerp
       (spg12-l-strspn address other)))
     (implies
      (integerp index)
      (integerp
       (spg12-allocation index)))
     (implies
      (integerp base)
      (integerp
       (spg12-region base)))
     (implies
      (integerp value)
      (integerp
       (spg12-to-uint64 value))))))

(defun spg12-addr-le-p (left right)
  (if (spg12-addr-le-op left right) t nil))

(defun spg12-addr-lt-p (left right)
  (if (spg12-addr-lt-op left right) t nil))

;; On addresses with equal bases, the source address relations are exactly
;; mathematical-integer order on offsets.

(defun-sk spg12-address-order-laws-p ()
  (forall (left right)
    (implies
     (and
      (spg12-address-p left)
      (spg12-address-p right)
      (equal
       (spg12-address-base left)
       (spg12-address-base right)))
     (and
      (equal
       (spg12-addr-le-p left right)
       (<=
        (spg12-address-offset left)
        (spg12-address-offset right)))
      (equal
       (spg12-addr-lt-p left right)
       (<
        (spg12-address-offset left)
        (spg12-address-offset right)))))))

(defun spg12-linked-p ()
  (if (spg12-linked-op) t nil))

(defun spg12-sconst-p ()
  (if (spg12-sconst-op) t nil))

;; Exact mathematical ranges for the source C integer predicates.

(defun spg12-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun spg12-is-uint64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; Universal range, identity-on-range, and projection laws for the source's
;; abstract Cint.to_uint64 operation used by logical strlen.

(defun-sk spg12-to-uint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (spg12-is-uint64-p
       (spg12-to-uint64 value))
      (implies
       (spg12-is-uint64-p value)
       (equal
        (spg12-to-uint64 value)
        value))
      (equal
       (spg12-to-uint64
        (spg12-to-uint64 value))
       (spg12-to-uint64 value))))))

;; Exact unfolding of Memory.valid_rw for the arbitrary allocation map t.

(defun spg12-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0
       (spg12-address-base address))
    (<= 0
        (spg12-address-offset address))
    (<=
     (+ (spg12-address-offset address)
        length)
     (spg12-allocation
      (spg12-address-base address))))))

;; Exact unfolding of A_Strlen.p_valid_str. The terminating position remains
;; an internal existential over all mathematical integers, and its character
;; range condition remains universally quantified over all integers.

(defun-sk spg12-string-chars-sint8-through-p
    (address bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position bound)
      (spg12-is-sint8-p
       (spg12-character-memory
        (spg12-shift address position)))))))

(defun-sk spg12-valid-string-p (address)
  (exists (index)
    (and
     (integerp index)
     (equal
      (spg12-character-memory
       (spg12-shift address index))
      0)
     (spg12-is-uint64-p index)
     (spg12-valid-rw-p
      (spg12-shift address 0)
      (+ 1 index))
     (spg12-string-chars-sint8-through-p
      address index))))

;; Universal closures of A_Strlen.fix_l_strlen and Q_TL_strlen.

(defun-sk spg12-strlen-laws-p ()
  (forall (address)
    (implies
     (spg12-address-p address)
     (and
      (if
          (equal
           (spg12-character-memory
            (spg12-shift address 0))
           0)
          (equal
           (spg12-l-strlen address)
           0)
        (equal
         (spg12-to-uint64
          (+ 1
             (spg12-l-strlen
              (spg12-shift address 1))))
         (spg12-l-strlen address)))
      (spg12-is-uint64-p
       (spg12-l-strlen address))))))

;; Exact unfolding of A_StrSpn.p_in_array. Its witness remains existentially
;; quantified over the full source address type.

(defun-sk spg12-in-array-p (start value)
  (exists (candidate)
    (and
     (spg12-address-p candidate)
     (equal
      (spg12-character-memory candidate)
      value)
     (spg12-addr-le-p start candidate)
     (spg12-addr-lt-p
      candidate
      (spg12-shift
       start
       (spg12-l-strlen start))))))

;; Exact universal closures of the three A_StrSpn axioms.

(defun-sk spg12-strspn-laws-p ()
  (forall (string accept)
    (implies
     (and
      (spg12-address-p string)
      (spg12-address-p accept))
     (and
      (implies
       (equal
        (spg12-character-memory string)
        0)
       (equal
        (spg12-l-strspn string accept)
        0))
      (implies
       (and
        (not
         (equal
          (spg12-character-memory string)
          0))
        (not
         (spg12-in-array-p
          accept
          (spg12-character-memory string))))
       (equal
        (spg12-l-strspn string accept)
        0))
      (implies
       (and
        (not
         (equal
          (spg12-character-memory string)
          0))
        (spg12-in-array-p
         accept
         (spg12-character-memory string)))
       (equal
        (+ 1
           (spg12-l-strspn
            (spg12-shift string 1)
            accept))
        (spg12-l-strspn string accept)))))))

;; The source's no-match hypothesis remains universal over every address.

(defun-sk spg12-no-match-before-p
    (start current value)
  (forall (candidate)
    (implies
     (spg12-address-p candidate)
     (implies
      (spg12-addr-lt-p candidate current)
      (implies
       (spg12-addr-le-p start candidate)
       (not
        (equal
         value
         (spg12-character-memory candidate))))))))

;; For each source-prefix address, the matching accept-string address remains
;; an internal existential over the full address type.

(defun-sk spg12-accept-witness-p
    (source-candidate accept-start accept-end)
  (exists (accept-candidate)
    (and
     (spg12-address-p accept-candidate)
     (equal
      (spg12-character-memory source-candidate)
      (spg12-character-memory accept-candidate))
     (spg12-addr-le-p
      accept-start
      accept-candidate)
     (spg12-addr-lt-p
      accept-candidate
      accept-end))))

(defun-sk spg12-prefix-values-in-accept-p
    (source-start source-current accept-start accept-end)
  (forall (source-candidate)
    (implies
     (spg12-address-p source-candidate)
     (implies
      (spg12-addr-lt-p
       source-candidate
       source-current)
      (implies
       (spg12-addr-le-p
        source-start
        source-candidate)
       (spg12-accept-witness-p
        source-candidate
        accept-start
        accept-end))))))

(defun-sk ntp4vc-strspn-loop-inv-7-preserved-goal12-statement ()
  (forall
   (a1 a3 a a2)
   (implies
    (and
     (spg12-address-p a1)
     (spg12-address-p a3)
     (spg12-address-p a)
     (spg12-address-p a2)
     (spg12-function-types-p)
     (spg12-address-order-laws-p)
     (spg12-to-uint64-laws-p)
     (spg12-strlen-laws-p)
     (spg12-strspn-laws-p))
    (let*
        ((x
          (spg12-character-memory a1))
         (x1
          (spg12-character-memory a3))
         (x2
          (spg12-address-offset a1))
         (x3
          (spg12-address-offset a))
         (x4
          (spg12-l-strlen a))
         (a4
          (spg12-shift
           a2
           (spg12-l-strlen a2)))
         (a5
          (spg12-shift a3 1)))
      (implies
       (and
        (not (equal x 0))
        (not (equal x1 0))
        (not (equal x1 x))
        (equal
         (+ x2
            (spg12-l-strspn a1 a2))
         (+ x3
            (spg12-l-strspn a a2)))
        (<= x3 x2)
        (<=
         (spg12-region
          (spg12-address-base a))
         0)
        (<=
         (spg12-region
          (spg12-address-base a2))
         0)
        (<= x2 (+ x3 x4))
        (spg12-linked-p)
        (spg12-sconst-p)
        (spg12-addr-le-p a a1)
        (spg12-addr-le-p a2 a3)
        (spg12-is-sint8-p x)
        (spg12-is-sint8-p x1)
        (spg12-valid-string-p a)
        (spg12-valid-string-p a1)
        (spg12-valid-string-p a2)
        (spg12-valid-string-p a3)
        (spg12-is-uint64-p (- x2 x3))
        (spg12-addr-le-p
         a1
         (spg12-shift a x4))
        (spg12-addr-le-p a3 a4)
        (implies
         (spg12-in-array-p a2 x)
         (spg12-in-array-p a3 x))
        (spg12-no-match-before-p
         a2 a3 x)
        (spg12-prefix-values-in-accept-p
         a a1 a2 a4))
       (and
        (spg12-addr-le-p a2 a5)
        (spg12-addr-le-p a5 a4)))))))

(value-triple :itpeval-statement-checked)

:q
