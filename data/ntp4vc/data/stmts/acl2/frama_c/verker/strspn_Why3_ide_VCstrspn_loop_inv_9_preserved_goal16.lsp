;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/verker/strspn_Why3_ide_VCstrspn_loop_inv_9_preserved_goal16:
;; preservation of the valid-string property after advancing the current accept
;; address by one, under the stated strspn loop, address-order, string,
;; membership-transfer, and quantified prefix hypotheses.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun spsg16-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun spsg16-address-base (address)
  (car address))

(defun spsg16-address-offset (address)
  (cdr address))

(defun spsg16-shift (address amount)
  (cons
   (spsg16-address-base address)
   (+ (spsg16-address-offset address)
      amount)))

;; Conservative interfaces represent the universally arbitrary character
;; memory t_1 and allocation map t, together with the source's region,
;; address-order, logical strlen, logical strspn, unsigned conversion,
;; linkedness, and constancy symbols.

(defstub spsg16-character-memory (address) t)
(defstub spsg16-allocation (index) t)
(defstub spsg16-region (base) t)
(defstub spsg16-addr-le-op (left right) t)
(defstub spsg16-addr-lt-op (left right) t)
(defstub spsg16-l-strlen (address) t)
(defstub spsg16-l-strspn (string accept) t)
(defstub spsg16-to-uint64 (value) t)
(defstub spsg16-linked-op () t)
(defstub spsg16-sconst-op () t)

;; Preserve the source function types over the full address and unbounded
;; mathematical-integer domains.

(defun-sk spsg16-function-types-p ()
  (forall (address other index base value)
    (and
     (implies
      (spsg16-address-p address)
      (and
       (integerp
        (spsg16-character-memory address))
       (integerp
        (spsg16-l-strlen address))))
     (implies
      (and
       (spsg16-address-p address)
       (spsg16-address-p other))
      (integerp
       (spsg16-l-strspn address other)))
     (implies
      (integerp index)
      (integerp
       (spsg16-allocation index)))
     (implies
      (integerp base)
      (integerp
       (spsg16-region base)))
     (implies
      (integerp value)
      (integerp
       (spsg16-to-uint64 value))))))

(defun spsg16-addr-le-p (left right)
  (if (spsg16-addr-le-op left right) t nil))

(defun spsg16-addr-lt-p (left right)
  (if (spsg16-addr-lt-op left right) t nil))

;; On addresses with equal bases, the source address relations are exactly
;; mathematical-integer order on offsets.

(defun-sk spsg16-address-order-laws-p ()
  (forall (left right)
    (implies
     (and
      (spsg16-address-p left)
      (spsg16-address-p right)
      (equal
       (spsg16-address-base left)
       (spsg16-address-base right)))
     (and
      (equal
       (spsg16-addr-le-p left right)
       (<=
        (spsg16-address-offset left)
        (spsg16-address-offset right)))
      (equal
       (spsg16-addr-lt-p left right)
       (<
        (spsg16-address-offset left)
        (spsg16-address-offset right)))))))

(defun spsg16-linked-p ()
  (if (spsg16-linked-op) t nil))

(defun spsg16-sconst-p ()
  (if (spsg16-sconst-op) t nil))

;; Exact mathematical ranges for the source C integer predicates.

(defun spsg16-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun spsg16-is-uint64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; Universal range, identity-on-range, and projection laws for the source's
;; abstract Cint.to_uint64 operation used by logical strlen.

(defun-sk spsg16-to-uint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (spsg16-is-uint64-p
       (spsg16-to-uint64 value))
      (implies
       (spsg16-is-uint64-p value)
       (equal
        (spsg16-to-uint64 value)
        value))
      (equal
       (spsg16-to-uint64
        (spsg16-to-uint64 value))
       (spsg16-to-uint64 value))))))

;; Exact unfolding of Memory.valid_rw for the arbitrary allocation map t.

(defun spsg16-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0
       (spsg16-address-base address))
    (<= 0
        (spsg16-address-offset address))
    (<=
     (+ (spsg16-address-offset address)
        length)
     (spsg16-allocation
      (spsg16-address-base address))))))

;; Exact unfolding of A_Strlen.p_valid_str. The terminating position remains
;; an internal existential over all mathematical integers, and its character
;; range condition remains universally quantified over all integers.

(defun-sk spsg16-string-chars-sint8-through-p
    (address bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position bound)
      (spsg16-is-sint8-p
       (spsg16-character-memory
        (spsg16-shift address position)))))))

(defun-sk spsg16-valid-string-p (address)
  (exists (index)
    (and
     (integerp index)
     (equal
      (spsg16-character-memory
       (spsg16-shift address index))
      0)
     (spsg16-is-uint64-p index)
     (spsg16-valid-rw-p
      (spsg16-shift address 0)
      (+ 1 index))
     (spsg16-string-chars-sint8-through-p
      address index))))

;; Universal closures of A_Strlen.fix_l_strlen and Q_TL_strlen.

(defun-sk spsg16-strlen-laws-p ()
  (forall (address)
    (implies
     (spsg16-address-p address)
     (and
      (if
          (equal
           (spsg16-character-memory
            (spsg16-shift address 0))
           0)
          (equal
           (spsg16-l-strlen address)
           0)
        (equal
         (spsg16-to-uint64
          (+ 1
             (spsg16-l-strlen
              (spsg16-shift address 1))))
         (spsg16-l-strlen address)))
      (spsg16-is-uint64-p
       (spsg16-l-strlen address))))))

;; Exact unfolding of A_StrSpn.p_in_array. Its witness remains existentially
;; quantified over the full source address type.

(defun-sk spsg16-in-array-p (start value)
  (exists (candidate)
    (and
     (spsg16-address-p candidate)
     (equal
      (spsg16-character-memory candidate)
      value)
     (spsg16-addr-le-p start candidate)
     (spsg16-addr-lt-p
      candidate
      (spsg16-shift
       start
       (spsg16-l-strlen start))))))

;; Exact universal closures of the three A_StrSpn axioms.

(defun-sk spsg16-strspn-laws-p ()
  (forall (string accept)
    (implies
     (and
      (spsg16-address-p string)
      (spsg16-address-p accept))
     (and
      (implies
       (equal
        (spsg16-character-memory string)
        0)
       (equal
        (spsg16-l-strspn string accept)
        0))
      (implies
       (and
        (not
         (equal
          (spsg16-character-memory string)
          0))
        (not
         (spsg16-in-array-p
          accept
          (spsg16-character-memory string))))
       (equal
        (spsg16-l-strspn string accept)
        0))
      (implies
       (and
        (not
         (equal
          (spsg16-character-memory string)
          0))
        (spsg16-in-array-p
         accept
         (spsg16-character-memory string)))
       (equal
        (+ 1
           (spsg16-l-strspn
            (spsg16-shift string 1)
            accept))
        (spsg16-l-strspn string accept)))))))

;; The source's no-match hypothesis remains universal over every address.

(defun-sk spsg16-no-match-before-p
    (start current value)
  (forall (candidate)
    (implies
     (spsg16-address-p candidate)
     (implies
      (spsg16-addr-lt-p candidate current)
      (implies
       (spsg16-addr-le-p start candidate)
       (not
        (equal
         value
         (spsg16-character-memory candidate))))))))

;; For each source-prefix address, the matching accept-string address remains
;; an internal existential over the full address type.

(defun-sk spsg16-accept-witness-p
    (source-candidate accept-start accept-end)
  (exists (accept-candidate)
    (and
     (spsg16-address-p accept-candidate)
     (equal
      (spsg16-character-memory source-candidate)
      (spsg16-character-memory accept-candidate))
     (spsg16-addr-le-p
      accept-start
      accept-candidate)
     (spsg16-addr-lt-p
      accept-candidate
      accept-end))))

(defun-sk spsg16-prefix-values-in-accept-p
    (source-start source-current accept-start accept-end)
  (forall (source-candidate)
    (implies
     (spsg16-address-p source-candidate)
     (implies
      (spsg16-addr-lt-p
       source-candidate
       source-current)
      (implies
       (spsg16-addr-le-p
        source-start
        source-candidate)
       (spsg16-accept-witness-p
        source-candidate
        accept-start
        accept-end))))))

(defun-sk
    ntp4vc-strspn-loop-inv-9-preserved-goal16-statement ()
  (forall
   (a1 a3 a a2)
   (implies
    (and
     (spsg16-address-p a1)
     (spsg16-address-p a3)
     (spsg16-address-p a)
     (spsg16-address-p a2)
     (spsg16-function-types-p)
     (spsg16-address-order-laws-p)
     (spsg16-to-uint64-laws-p)
     (spsg16-strlen-laws-p)
     (spsg16-strspn-laws-p))
    (let*
        ((x
          (spsg16-character-memory a1))
         (x1
          (spsg16-character-memory a3))
         (x2
          (spsg16-address-offset a1))
         (x3
          (spsg16-address-offset a))
         (x4
          (spsg16-l-strlen a))
         (a4
          (spsg16-shift
           a2
           (spsg16-l-strlen a2))))
      (implies
       (and
        (not (equal x 0))
        (not (equal x1 0))
        (not (equal x1 x))
        (equal
         (+ x2
            (spsg16-l-strspn a1 a2))
         (+ x3
            (spsg16-l-strspn a a2)))
        (<= x3 x2)
        (<=
         (spsg16-region
          (spsg16-address-base a))
         0)
        (<=
         (spsg16-region
          (spsg16-address-base a2))
         0)
        (<= x2 (+ x3 x4))
        (spsg16-linked-p)
        (spsg16-sconst-p)
        (spsg16-addr-le-p a a1)
        (spsg16-addr-le-p a2 a3)
        (spsg16-is-sint8-p x)
        (spsg16-is-sint8-p x1)
        (spsg16-valid-string-p a)
        (spsg16-valid-string-p a1)
        (spsg16-valid-string-p a2)
        (spsg16-valid-string-p a3)
        (spsg16-is-uint64-p (- x2 x3))
        (spsg16-addr-le-p
         a1
         (spsg16-shift a x4))
        (spsg16-addr-le-p a3 a4)
        (implies
         (spsg16-in-array-p a2 x)
         (spsg16-in-array-p a3 x))
        (spsg16-no-match-before-p
         a2 a3 x)
        (spsg16-prefix-values-in-accept-p
         a a1 a2 a4))
       (spsg16-valid-string-p
        (spsg16-shift a3 1)))))))

(value-triple :itpeval-statement-checked)

:q
