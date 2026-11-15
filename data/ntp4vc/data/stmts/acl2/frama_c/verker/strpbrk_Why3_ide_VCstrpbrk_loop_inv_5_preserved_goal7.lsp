;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/verker/strpbrk_Why3_ide_VCstrpbrk_loop_inv_5_preserved_goal7:
;; preservation of the strpbrk loop invariant that advancing the current
;; address by one remains within the second string's logical bounds, under
;; the stated string, byte-range, membership, and no-match hypotheses.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun spvi5g7-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun spvi5g7-address-base (address)
  (car address))

(defun spvi5g7-address-offset (address)
  (cdr address))

(defun spvi5g7-shift (address amount)
  (cons
   (spvi5g7-address-base address)
   (+ (spvi5g7-address-offset address)
      amount)))

(defun spvi5g7-null-address ()
  (cons 0 0))

;; Conservative interfaces represent the universally arbitrary character
;; memory t_1 and allocation map t, together with the source's region,
;; address-order, logical strlen, logical strpbrk, unsigned conversion,
;; linkedness, and constancy symbols.

(defstub spvi5g7-character-memory (address) t)
(defstub spvi5g7-allocation (index) t)
(defstub spvi5g7-region (base) t)
(defstub spvi5g7-addr-le-op (left right) t)
(defstub spvi5g7-addr-lt-op (left right) t)
(defstub spvi5g7-l-strlen (address) t)
(defstub spvi5g7-l-strpbrk (string accept) t)
(defstub spvi5g7-to-uint64 (value) t)
(defstub spvi5g7-linked-op () t)
(defstub spvi5g7-sconst-op () t)

;; Preserve the source function types over the full address and unbounded
;; mathematical-integer domains.

(defun-sk spvi5g7-function-types-p ()
  (forall (address other index base value)
    (and
     (implies
      (spvi5g7-address-p address)
      (and
       (integerp
        (spvi5g7-character-memory address))
       (integerp
        (spvi5g7-l-strlen address))))
     (implies
      (and
       (spvi5g7-address-p address)
       (spvi5g7-address-p other))
      (spvi5g7-address-p
       (spvi5g7-l-strpbrk address other)))
     (implies
      (integerp index)
      (integerp
       (spvi5g7-allocation index)))
     (implies
      (integerp base)
      (integerp
       (spvi5g7-region base)))
     (implies
      (integerp value)
      (integerp
       (spvi5g7-to-uint64 value))))))

(defun spvi5g7-addr-le-p (left right)
  (if (spvi5g7-addr-le-op left right) t nil))

(defun spvi5g7-addr-lt-p (left right)
  (if (spvi5g7-addr-lt-op left right) t nil))

;; On addresses with equal bases, the source address relations are exactly
;; mathematical-integer order on offsets.

(defun-sk spvi5g7-address-order-laws-p ()
  (forall (left right)
    (implies
     (and
      (spvi5g7-address-p left)
      (spvi5g7-address-p right)
      (equal
       (spvi5g7-address-base left)
       (spvi5g7-address-base right)))
     (and
      (equal
       (spvi5g7-addr-le-p left right)
       (<=
        (spvi5g7-address-offset left)
        (spvi5g7-address-offset right)))
      (equal
       (spvi5g7-addr-lt-p left right)
       (<
        (spvi5g7-address-offset left)
        (spvi5g7-address-offset right)))))))

(defun spvi5g7-linked-p ()
  (if (spvi5g7-linked-op) t nil))

(defun spvi5g7-sconst-p ()
  (if (spvi5g7-sconst-op) t nil))

;; Exact mathematical ranges for the source C integer predicates.

(defun spvi5g7-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun spvi5g7-is-uint64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; Universal range, identity-on-range, and projection laws for the source's
;; abstract Cint.to_uint64 operation used by logical strlen.

(defun-sk spvi5g7-to-uint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (spvi5g7-is-uint64-p
       (spvi5g7-to-uint64 value))
      (implies
       (spvi5g7-is-uint64-p value)
       (equal
        (spvi5g7-to-uint64 value)
        value))
      (equal
       (spvi5g7-to-uint64
        (spvi5g7-to-uint64 value))
       (spvi5g7-to-uint64 value))))))

;; Exact unfolding of Memory.valid_rw for the arbitrary allocation map t.

(defun spvi5g7-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0
       (spvi5g7-address-base address))
    (<= 0
        (spvi5g7-address-offset address))
    (<=
     (+ (spvi5g7-address-offset address)
        length)
     (spvi5g7-allocation
      (spvi5g7-address-base address))))))

;; Exact unfolding of A_Strlen.p_valid_str. The terminating position remains
;; an internal existential over all mathematical integers, and its character
;; range condition remains universally quantified over all integers.

(defun-sk spvi5g7-string-chars-sint8-through-p
    (address bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position bound)
      (spvi5g7-is-sint8-p
       (spvi5g7-character-memory
        (spvi5g7-shift address position)))))))

(defun-sk spvi5g7-valid-string-p (address)
  (exists (index)
    (and
     (integerp index)
     (equal
      (spvi5g7-character-memory
       (spvi5g7-shift address index))
      0)
     (spvi5g7-is-uint64-p index)
     (spvi5g7-valid-rw-p
      (spvi5g7-shift address 0)
      (+ 1 index))
     (spvi5g7-string-chars-sint8-through-p
      address index))))

;; Universal closures of A_Strlen.fix_l_strlen and Q_TL_strlen.

(defun-sk spvi5g7-strlen-laws-p ()
  (forall (address)
    (implies
     (spvi5g7-address-p address)
     (and
      (if
          (equal
           (spvi5g7-character-memory
            (spvi5g7-shift address 0))
           0)
          (equal
           (spvi5g7-l-strlen address)
           0)
        (equal
         (spvi5g7-to-uint64
          (+ 1
             (spvi5g7-l-strlen
              (spvi5g7-shift address 1))))
         (spvi5g7-l-strlen address)))
      (spvi5g7-is-uint64-p
       (spvi5g7-l-strlen address))))))

;; Exact unfolding of A_StrSpn.p_in_array. Its witness remains existentially
;; quantified over the full source address type.

(defun-sk spvi5g7-in-array-p (start value)
  (exists (candidate)
    (and
     (spvi5g7-address-p candidate)
     (equal
      (spvi5g7-character-memory candidate)
      value)
     (spvi5g7-addr-le-p start candidate)
     (spvi5g7-addr-lt-p
      candidate
      (spvi5g7-shift
       start
       (spvi5g7-l-strlen start))))))

;; Exact universal closures of the three A_StrPBrk axioms.

(defun-sk spvi5g7-strpbrk-laws-p ()
  (forall (string accept)
    (implies
     (and
      (spvi5g7-address-p string)
      (spvi5g7-address-p accept))
     (and
      (implies
       (equal
        (spvi5g7-character-memory string)
        0)
       (equal
        (spvi5g7-l-strpbrk string accept)
        (spvi5g7-null-address)))
      (implies
       (and
        (not
         (equal
          (spvi5g7-character-memory string)
          0))
        (spvi5g7-in-array-p
         accept
         (spvi5g7-character-memory string)))
       (equal
        (spvi5g7-l-strpbrk string accept)
        string))
      (implies
       (and
        (not
         (equal
          (spvi5g7-character-memory string)
          0))
        (not
         (spvi5g7-in-array-p
          accept
          (spvi5g7-character-memory string))))
       (equal
        (spvi5g7-l-strpbrk
         (spvi5g7-shift string 1)
         accept)
        (spvi5g7-l-strpbrk string accept)))))))

;; The source's two quantified no-match hypotheses remain universal over
;; every address rather than being replaced by external witnesses.

(defun-sk spvi5g7-no-value-before-current-p
    (start current value)
  (forall (candidate)
    (implies
     (spvi5g7-address-p candidate)
     (implies
      (spvi5g7-addr-lt-p candidate current)
      (implies
       (spvi5g7-addr-le-p start candidate)
       (not
        (equal
         value
         (spvi5g7-character-memory candidate))))))))

(defun-sk spvi5g7-cross-values-distinct-p
    (first-start first-current second-start second-end)
  (forall (first-candidate second-candidate)
    (implies
     (and
      (spvi5g7-address-p first-candidate)
      (spvi5g7-address-p second-candidate))
     (implies
      (spvi5g7-addr-lt-p first-candidate first-current)
      (implies
       (spvi5g7-addr-le-p second-start second-candidate)
       (implies
        (spvi5g7-addr-le-p first-start first-candidate)
        (implies
         (spvi5g7-addr-lt-p second-candidate second-end)
         (not
          (equal
           (spvi5g7-character-memory first-candidate)
           (spvi5g7-character-memory second-candidate))))))))))

(defun-sk
    ntp4vc-strpbrk-loop-inv-5-preserved-goal7-statement ()
  (forall
   (a a1 a2 a3)
   (implies
    (and
     (spvi5g7-address-p a)
     (spvi5g7-address-p a1)
     (spvi5g7-address-p a2)
     (spvi5g7-address-p a3)
     (spvi5g7-function-types-p)
     (spvi5g7-address-order-laws-p)
     (spvi5g7-to-uint64-laws-p)
     (spvi5g7-strlen-laws-p)
     (spvi5g7-strpbrk-laws-p))
    (let*
        ((x
          (spvi5g7-character-memory a))
         (x1
          (spvi5g7-character-memory a1))
         (a4
          (spvi5g7-shift
           a2
           (spvi5g7-l-strlen a2)))
         (a5
          (spvi5g7-shift a 1)))
      (implies
       (and
        (not (equal x 0))
        (not (equal x1 0))
        (not (equal x1 x))
        (equal
         (spvi5g7-l-strpbrk a3 a2)
         (spvi5g7-l-strpbrk a1 a2))
        (<=
         (spvi5g7-region
          (spvi5g7-address-base a2))
         0)
        (<=
         (spvi5g7-region
          (spvi5g7-address-base a3))
         0)
        (spvi5g7-linked-p)
        (spvi5g7-sconst-p)
        (spvi5g7-addr-le-p a2 a)
        (spvi5g7-addr-le-p a3 a1)
        (spvi5g7-is-sint8-p x)
        (spvi5g7-is-sint8-p x1)
        (spvi5g7-valid-string-p a)
        (spvi5g7-valid-string-p a1)
        (spvi5g7-valid-string-p a2)
        (spvi5g7-valid-string-p a3)
        (spvi5g7-addr-le-p a a4)
        (spvi5g7-addr-le-p
         a1
         (spvi5g7-shift
          a3
          (spvi5g7-l-strlen a3)))
        (implies
         (spvi5g7-in-array-p a2 x1)
         (spvi5g7-in-array-p a x1))
        (spvi5g7-no-value-before-current-p
         a2 a x1)
        (spvi5g7-cross-values-distinct-p
         a3 a1 a2 a4))
       (and
        (spvi5g7-addr-le-p a2 a5)
        (spvi5g7-addr-le-p a5 a4)))))))

(value-triple :itpeval-statement-checked)

:q
