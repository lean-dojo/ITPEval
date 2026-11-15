;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/verker/strcat_Why3_ide_VCstrcat_loop_inv_2_preserved_goal3:
;; preservation of valid-string memory after advancing the current strcat
;; pointer by one, under the stated string, allocation, address-order,
;; linkedness, character-range, and non-null-prefix hypotheses. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun scvip3-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun scvip3-address-base (address)
  (car address))

(defun scvip3-address-offset (address)
  (cdr address))

(defun scvip3-shift (address amount)
  (cons
   (scvip3-address-base address)
   (+ (scvip3-address-offset address) amount)))

;; Conservative interfaces represent the universally arbitrary character
;; memory t_1, allocation map t, region function, address-order relation,
;; logical strlen function, unsigned conversion, and the linked and sconst
;; predicates specialized respectively to t and t_1.

(defstub scvip3-character-memory (address) t)
(defstub scvip3-allocation (index) t)
(defstub scvip3-region (base) t)
(defstub scvip3-addr-le-op (left right) t)
(defstub scvip3-l-strlen (address) t)
(defstub scvip3-to-uint64 (value) t)
(defstub scvip3-linked-op () t)
(defstub scvip3-sconst-op () t)

;; Preserve the source function types over the full address and unbounded
;; mathematical-integer domains.

(defun-sk scvip3-function-types-p ()
  (forall (address index base)
    (and
     (implies
      (scvip3-address-p address)
      (and
       (integerp
        (scvip3-character-memory address))
       (integerp
        (scvip3-l-strlen address))))
     (implies
      (integerp index)
      (integerp
       (scvip3-allocation index)))
     (implies
      (integerp base)
      (integerp
       (scvip3-region base))))))

(defun scvip3-addr-le-p (left right)
  (if (scvip3-addr-le-op left right) t nil))

;; Exact source law for address order: when two addresses have the same base,
;; addr_le is precisely mathematical-integer order on their offsets.

(defun-sk scvip3-address-order-law-p ()
  (forall (left right)
    (implies
     (and
      (scvip3-address-p left)
      (scvip3-address-p right)
      (equal
       (scvip3-address-base left)
       (scvip3-address-base right)))
     (equal
      (scvip3-addr-le-p left right)
      (<=
       (scvip3-address-offset left)
       (scvip3-address-offset right))))))

(defun scvip3-linked-p ()
  (if (scvip3-linked-op) t nil))

(defun scvip3-sconst-p ()
  (if (scvip3-sconst-op) t nil))

;; Exact mathematical ranges for the source C integer predicates.

(defun scvip3-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun scvip3-is-uint64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; Universal range, identity-on-range, and projection laws for the source's
;; abstract Cint.to_uint64 operation.

(defun-sk scvip3-to-uint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (scvip3-is-uint64-p
       (scvip3-to-uint64 value))
      (implies
       (scvip3-is-uint64-p value)
       (equal
        (scvip3-to-uint64 value)
        value))
      (equal
       (scvip3-to-uint64
        (scvip3-to-uint64 value))
       (scvip3-to-uint64 value))))))

;; Exact unfolding of Memory.valid_rw for the arbitrary allocation map t.

(defun scvip3-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (scvip3-address-base address))
    (<= 0 (scvip3-address-offset address))
    (<=
     (+ (scvip3-address-offset address) length)
     (scvip3-allocation
      (scvip3-address-base address))))))

;; Exact unfolding of A_Strlen.p_valid_str. The terminating index remains an
;; internal existential over all mathematical integers.

(defun-sk scvip3-string-chars-sint8-through-p
    (address bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position bound)
      (scvip3-is-sint8-p
       (scvip3-character-memory
        (scvip3-shift address position)))))))

(defun-sk scvip3-valid-string-p (address)
  (exists (index)
    (and
     (integerp index)
     (equal
      (scvip3-character-memory
       (scvip3-shift address index))
      0)
     (scvip3-is-uint64-p index)
     (scvip3-valid-rw-p
      (scvip3-shift address 0)
      (+ 1 index))
     (scvip3-string-chars-sint8-through-p
      address index))))

;; Universal closures of A_Strlen.fix_l_strlen and Q_TL_strlen.

(defun-sk scvip3-strlen-laws-p ()
  (forall (address)
    (implies
     (scvip3-address-p address)
     (and
      (if
          (equal
           (scvip3-character-memory
            (scvip3-shift address 0))
           0)
          (equal
           (scvip3-l-strlen address)
           0)
        (equal
         (scvip3-to-uint64
          (+ 1
             (scvip3-l-strlen
              (scvip3-shift address 1))))
         (scvip3-l-strlen address)))
      (scvip3-is-uint64-p
       (scvip3-l-strlen address))))))

;; The two loop hypotheses retain their internal universal quantifiers over
;; every mathematical-integer offset.

(defun-sk scvip3-no-null-before-length-p
    (address length)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= 0 position)
      (implies
       (< position length)
       (not
        (equal
         (scvip3-character-memory
          (scvip3-shift address position))
         0)))))))

(defun-sk scvip3-no-null-before-a2-offset-p
    (a a2)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= 0 position)
      (implies
       (<
        (+ position
           (scvip3-address-offset a))
        (scvip3-address-offset a2))
       (not
        (equal
         (scvip3-character-memory
          (scvip3-shift a position))
         0)))))))

(defun-sk
    ntp4vc-strcat-loop-inv-2-preserved-goal3-statement ()
  (forall
   (a2 a a1)
   (implies
    (and
     (scvip3-address-p a2)
     (scvip3-address-p a)
     (scvip3-address-p a1)
     (scvip3-function-types-p)
     (scvip3-address-order-law-p)
     (scvip3-to-uint64-laws-p)
     (scvip3-strlen-laws-p))
    (let*
        ((x
          (scvip3-character-memory a2))
         (x1
          (scvip3-l-strlen a))
         (a3
          (scvip3-shift a x1))
         (x2
          (scvip3-l-strlen a1)))
      (implies
       (and
        (not (equal x 0))
        (equal
         (scvip3-character-memory a3)
         0)
        (<=
         (scvip3-region
          (scvip3-address-base a))
         0)
        (<=
         (scvip3-region
          (scvip3-address-base a1))
         0)
        (<=
         (+ x1 x2)
         18446744073709551615)
        (scvip3-linked-p)
        (scvip3-sconst-p)
        (scvip3-addr-le-p a a2)
        (scvip3-is-sint8-p x)
        (scvip3-valid-string-p a)
        (scvip3-valid-string-p a1)
        (scvip3-valid-string-p a2)
        (scvip3-is-uint64-p x1)
        (scvip3-addr-le-p a2 a3)
        (scvip3-valid-rw-p
         (scvip3-shift a 0)
         (+ 1 x1 x2))
        (scvip3-no-null-before-length-p
         a x1)
        (scvip3-no-null-before-a2-offset-p
         a a2))
       (scvip3-valid-string-p
        (scvip3-shift a2 1)))))))

(value-triple :itpeval-statement-checked)

:q
