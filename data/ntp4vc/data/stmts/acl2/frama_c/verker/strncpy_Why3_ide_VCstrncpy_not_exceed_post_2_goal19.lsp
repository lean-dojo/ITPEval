;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/verker/strncpy_Why3_ide_VCstrncpy_not_exceed_post_2_goal19:
;; the strncpy not-exceed postcondition concluding bounded-string validity at
;; the destination start, under the stated havoc, address-order, allocation,
;; source-string, destination-string, and copied-prefix hypotheses.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun snp2g19-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun snp2g19-address-base (address)
  (car address))

(defun snp2g19-address-offset (address)
  (cdr address))

(defun snp2g19-shift (address amount)
  (cons
   (snp2g19-address-base address)
   (+ (snp2g19-address-offset address)
      amount)))

;; Conservative interfaces represent the universally arbitrary character
;; memories t_1, t_2, and t_3 and allocation map t, together with the source
;; region, address-order, logical strlen and strnlen, C conversion, linkedness,
;; and constancy symbols.

(defstub snp2g19-t1 (address) t)
(defstub snp2g19-t2 (address) t)
(defstub snp2g19-t3 (address) t)
(defstub snp2g19-allocation (index) t)
(defstub snp2g19-region (base) t)
(defstub snp2g19-addr-le-op (left right) t)
(defstub snp2g19-l-strlen-t2 (address) t)
(defstub snp2g19-l-strnlen-t2 (address count) t)
(defstub snp2g19-l-strnlen-t3 (address count) t)
(defstub snp2g19-to-uint64 (value) t)
(defstub snp2g19-linked-op () t)
(defstub snp2g19-sconst-op () t)

;; Preserve the source function types over the full address and unbounded
;; mathematical-integer domains.

(defun-sk snp2g19-function-types-p ()
  (forall (address index base count value)
    (and
     (implies
      (snp2g19-address-p address)
      (and
       (integerp (snp2g19-t1 address))
       (integerp (snp2g19-t2 address))
       (integerp (snp2g19-t3 address))
       (integerp
        (snp2g19-l-strlen-t2 address))
       (implies
        (integerp count)
        (and
         (integerp
          (snp2g19-l-strnlen-t2
           address count))
         (integerp
          (snp2g19-l-strnlen-t3
           address count))))))
     (implies
      (integerp index)
      (integerp
       (snp2g19-allocation index)))
     (implies
      (integerp base)
      (integerp
       (snp2g19-region base)))
     (implies
      (integerp value)
      (integerp
       (snp2g19-to-uint64 value))))))

(defun snp2g19-addr-le-p (left right)
  (if (snp2g19-addr-le-op left right) t nil))

;; On addresses with equal bases, the source address relation is exactly
;; mathematical-integer order on offsets.

(defun-sk snp2g19-address-order-law-p ()
  (forall (left right)
    (implies
     (and
      (snp2g19-address-p left)
      (snp2g19-address-p right)
      (equal
       (snp2g19-address-base left)
       (snp2g19-address-base right)))
     (equal
      (snp2g19-addr-le-p left right)
      (<=
       (snp2g19-address-offset left)
       (snp2g19-address-offset right))))))

(defun snp2g19-linked-p ()
  (if (snp2g19-linked-op) t nil))

(defun snp2g19-sconst-p ()
  (if (snp2g19-sconst-op) t nil))

;; Exact mathematical ranges for the source C integer predicates.

(defun snp2g19-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun snp2g19-is-uint64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; Universal range, identity-on-range, and projection laws for the source
;; unsigned 64-bit conversion used by strlen and strnlen.

(defun-sk snp2g19-to-uint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (snp2g19-is-uint64-p
       (snp2g19-to-uint64 value))
      (implies
       (snp2g19-is-uint64-p value)
       (equal
        (snp2g19-to-uint64 value)
        value))
      (equal
       (snp2g19-to-uint64
        (snp2g19-to-uint64 value))
       (snp2g19-to-uint64 value))))))

;; Exact unfoldings of Memory.valid_rw and Memory.separated.

(defun snp2g19-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0
       (snp2g19-address-base address))
    (<= 0
        (snp2g19-address-offset address))
    (<=
     (+ (snp2g19-address-offset address)
        length)
     (snp2g19-allocation
      (snp2g19-address-base address))))))

(defun snp2g19-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (snp2g19-address-base left)
     (snp2g19-address-base right)))
   (<=
    (+ (snp2g19-address-offset right)
       right-length)
    (snp2g19-address-offset left))
   (<=
    (+ (snp2g19-address-offset left)
       left-length)
    (snp2g19-address-offset right))))

;; Exact pointwise content of Memory.havoc_access. The source equality between
;; the resulting memory function and t_3 is represented extensionally over the
;; entire integer-pair address carrier.

(defun snp2g19-havoc-read
    (address start length)
  (if
      (snp2g19-separated-p
       address 1 start length)
      (snp2g19-t2 address)
    (snp2g19-t1 address)))

(defun-sk snp2g19-havoc-equals-t3-p
    (start length)
  (forall (address)
    (implies
     (snp2g19-address-p address)
     (equal
      (snp2g19-havoc-read
       address start length)
      (snp2g19-t3 address)))))

;; Exact unfoldings of A_Strlen.p_valid_str for t_2 and t_3. Each terminating
;; position remains internally existential, and each character-range condition
;; remains universal over every mathematical integer.

(defun-sk snp2g19-t2-string-chars-p
    (address bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position bound)
      (snp2g19-is-sint8-p
       (snp2g19-t2
        (snp2g19-shift
         address position)))))))

(defun-sk snp2g19-t2-valid-string-p
    (address)
  (exists (index)
    (and
     (integerp index)
     (equal
      (snp2g19-t2
       (snp2g19-shift address index))
      0)
     (snp2g19-is-uint64-p index)
     (snp2g19-valid-rw-p
      (snp2g19-shift address 0)
      (+ 1 index))
     (snp2g19-t2-string-chars-p
      address index))))

(defun-sk snp2g19-t3-string-chars-p
    (address bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position bound)
      (snp2g19-is-sint8-p
       (snp2g19-t3
        (snp2g19-shift
         address position)))))))

(defun-sk snp2g19-t3-valid-string-p
    (address)
  (exists (index)
    (and
     (integerp index)
     (equal
      (snp2g19-t3
       (snp2g19-shift address index))
      0)
     (snp2g19-is-uint64-p index)
     (snp2g19-valid-rw-p
      (snp2g19-shift address 0)
      (+ 1 index))
     (snp2g19-t3-string-chars-p
      address index))))

;; Exact unfoldings of A_Strnlen.p_valid_strn. The source disjunction and all
;; existential and universal quantifier scopes are preserved.

(defun-sk snp2g19-t2-bounded-zero-p
    (address count)
  (exists (index)
    (and
     (integerp index)
     (equal
      (snp2g19-t2
       (snp2g19-shift address index))
      0)
     (< index count)
     (snp2g19-is-uint64-p index)
     (snp2g19-valid-rw-p
      (snp2g19-shift address 0)
      (+ 1 index)))))

(defun-sk snp2g19-t2-bounded-chars-p
    (address count)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position count)
      (snp2g19-is-sint8-p
       (snp2g19-t2
        (snp2g19-shift
         address position)))))))

(defun snp2g19-t2-valid-bounded-string-p
    (address count)
  (or
   (snp2g19-valid-rw-p
    (snp2g19-shift address 0)
    (+ 1 count))
   (and
    (snp2g19-t2-bounded-zero-p
     address count)
    (snp2g19-t2-bounded-chars-p
     address count))))

(defun-sk snp2g19-t3-bounded-zero-p
    (address count)
  (exists (index)
    (and
     (integerp index)
     (equal
      (snp2g19-t3
       (snp2g19-shift address index))
      0)
     (< index count)
     (snp2g19-is-uint64-p index)
     (snp2g19-valid-rw-p
      (snp2g19-shift address 0)
      (+ 1 index)))))

(defun-sk snp2g19-t3-bounded-chars-p
    (address count)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position count)
      (snp2g19-is-sint8-p
       (snp2g19-t3
        (snp2g19-shift
         address position)))))))

(defun snp2g19-t3-valid-bounded-string-p
    (address count)
  (or
   (snp2g19-valid-rw-p
    (snp2g19-shift address 0)
    (+ 1 count))
   (and
    (snp2g19-t3-bounded-zero-p
     address count)
    (snp2g19-t3-bounded-chars-p
     address count))))

;; Universal closures of A_Strlen.fix_l_strlen, A_Strlen.Q_TL_strlen,
;; A_Strnlen.fix_l_strnlen, and A_Strnlen.Q_TL_strnlen for the memories used
;; by this verification condition.

(defun-sk snp2g19-t2-strlen-laws-p ()
  (forall (address)
    (implies
     (snp2g19-address-p address)
     (and
      (if
          (equal
           (snp2g19-t2
            (snp2g19-shift address 0))
           0)
          (equal
           (snp2g19-l-strlen-t2 address)
           0)
        (equal
         (snp2g19-to-uint64
          (+ 1
             (snp2g19-l-strlen-t2
              (snp2g19-shift
               address 1))))
         (snp2g19-l-strlen-t2 address)))
      (snp2g19-is-uint64-p
       (snp2g19-l-strlen-t2 address))))))

(defun-sk snp2g19-strnlen-laws-p ()
  (forall (address count)
    (implies
     (and
      (snp2g19-address-p address)
      (integerp count))
     (and
      (if
          (or
           (equal count 0)
           (equal
            (snp2g19-t2
             (snp2g19-shift address 0))
            0))
          (equal
           (snp2g19-l-strnlen-t2
            address count)
           0)
        (equal
         (snp2g19-to-uint64
          (+ 1
             (snp2g19-l-strnlen-t2
              (snp2g19-shift address 1)
              (snp2g19-to-uint64
               (- count 1)))))
         (snp2g19-l-strnlen-t2
          address count)))
      (snp2g19-is-uint64-p
       (snp2g19-l-strnlen-t2
        address count))
      (if
          (or
           (equal count 0)
           (equal
            (snp2g19-t3
             (snp2g19-shift address 0))
            0))
          (equal
           (snp2g19-l-strnlen-t3
            address count)
           0)
        (equal
         (snp2g19-to-uint64
          (+ 1
             (snp2g19-l-strnlen-t3
              (snp2g19-shift address 1)
              (snp2g19-to-uint64
               (- count 1)))))
         (snp2g19-l-strnlen-t3
          address count)))
      (snp2g19-is-uint64-p
       (snp2g19-l-strnlen-t3
        address count))))))

;; These extensional predicates preserve that l_strnlen is one function of a
;; memory, address, and count rather than unrelated symbols for t_2 and t_3.

(defun-sk snp2g19-t2-equals-t3-p ()
  (forall (address)
    (implies
     (snp2g19-address-p address)
     (equal
      (snp2g19-t2 address)
      (snp2g19-t3 address)))))

(defun-sk snp2g19-strnlen-extensionality-p ()
  (forall (address count)
    (implies
     (and
      (snp2g19-address-p address)
      (integerp count)
      (snp2g19-t2-equals-t3-p))
     (equal
      (snp2g19-l-strnlen-t2
       address count)
      (snp2g19-l-strnlen-t3
       address count)))))

;; The copied-prefix hypothesis retains its universal quantifier over every
;; mathematical integer and its strict bound using a_2's offset.

(defun-sk snp2g19-copied-prefix-p
    (source destination upper)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= 0 position)
      (implies
       (< (+ position
             (snp2g19-address-offset source))
          (snp2g19-address-offset upper))
       (equal
        (snp2g19-t3
         (snp2g19-shift
          source position))
        (snp2g19-t3
         (snp2g19-shift
          destination position))))))))

(defun-sk
    ntp4vc-strncpy-not-exceed-post-2-goal19-statement ()
  (forall
   (a3 a1 a a2)
   (implies
    (and
     (snp2g19-address-p a3)
     (snp2g19-address-p a1)
     (snp2g19-address-p a)
     (snp2g19-address-p a2)
     (snp2g19-function-types-p)
     (snp2g19-address-order-law-p)
     (snp2g19-to-uint64-laws-p)
     (snp2g19-t2-strlen-laws-p)
     (snp2g19-strnlen-laws-p)
     (snp2g19-strnlen-extensionality-p))
    (let*
        ((x
          (snp2g19-address-base a3))
         (x1
          (snp2g19-address-base a1))
         (a4
          (snp2g19-shift a1 0))
         (x2
          (snp2g19-address-offset a1))
         (x3
          (snp2g19-address-offset a))
         (x4
          (- x3 x2)))
      (implies
       (and
        (not (equal x x1))
        (snp2g19-havoc-equals-t3-p
         a4
         (+ 1
            (snp2g19-l-strnlen-t3
             a3 0)))
        (<= x2 x3)
        (<= (snp2g19-region x1) 0)
        (<= (snp2g19-region x) 0)
        (< x3
           (+ x2
              (snp2g19-l-strlen-t2 a3)))
        (snp2g19-linked-p)
        (snp2g19-sconst-p)
        (snp2g19-addr-le-p a1 a)
        (snp2g19-addr-le-p a3 a2)
        (snp2g19-t2-valid-string-p a3)
        (snp2g19-t3-valid-string-p a2)
        (snp2g19-is-uint64-p x4)
        (snp2g19-t2-valid-bounded-string-p
         a3 x4)
        (snp2g19-t3-valid-bounded-string-p
         a x4)
        (snp2g19-addr-le-p
         a
         (snp2g19-shift a1 x4))
        (snp2g19-addr-le-p
         a2
         (snp2g19-shift
          a3
          (snp2g19-l-strnlen-t3
           a3 x4)))
        (snp2g19-valid-rw-p
         a4
         (+ 1
            (snp2g19-l-strnlen-t2
             a3 x4)))
        (snp2g19-copied-prefix-p
         a3 a1 a2))
       (snp2g19-t3-valid-bounded-string-p
        a1 x4))))))

(value-triple :itpeval-statement-checked)

:q
