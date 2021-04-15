; ****************** BEGIN INITIALIZATION FOR ACL2s MODE ****************** ;
; (Nothing to see here!  Your actual file is after this initialization code);
(make-event
 (er-progn
  (set-deferred-ttag-notes t state)
  (value '(value-triple :invisible))))

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading the CCG book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/ccg/ccg" :uncertified-okp nil :dir :system :ttags ((:ccg)) :load-compiled-file nil);v4.0 change

;Common base theory for all modes.
#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s base theory book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/base-theory" :dir :system :ttags :all)


#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s customizations book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/custom" :dir :system :ttags :all)

;; guard-checking-on is in *protected-system-state-globals* so any
;; changes are reverted back to what they were if you try setting this
;; with make-event. So, in order to avoid the use of progn! and trust
;; tags (which would not have been a big deal) in custom.lisp, I
;; decided to add this here.
;; 
;; How to check (f-get-global 'guard-checking-on state)
;; (acl2::set-guard-checking :nowarn)
(acl2::set-guard-checking :all)

;Settings common to all ACL2s modes
(acl2s-common-settings)
;(acl2::xdoc acl2s::defunc) ;; 3 seconds is too much time to spare -- commenting out [2015-02-01 Sun]

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s customizations book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/acl2s-sigs" :dir :system :ttags :all)

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem setting up ACL2s mode.") (value :invisible))

(acl2::xdoc acl2s::defunc) ; almost 3 seconds

; Non-events:
;(set-guard-checking :none)

(set-inhibit-warnings! "Invariant-risk" "theory")

(in-package "ACL2")
(redef+)
(defun print-ttag-note (val active-book-name include-bookp deferred-p state)
  (declare (xargs :stobjs state)
	   (ignore val active-book-name include-bookp deferred-p))
  state)

(defun print-deferred-ttag-notes-summary (state)
  (declare (xargs :stobjs state))
  state)

(defun notify-on-defttag (val active-book-name include-bookp state)
  (declare (xargs :stobjs state)
	   (ignore val active-book-name include-bookp))
  state)
(redef-)

(acl2::in-package "ACL2S")

; ******************* END INITIALIZATION FOR ACL2s MODE ******************* ;
;$ACL2s-SMode$;ACL2s

(defmacro let-match* (binds body)
  (case-match binds
    ('() body)
    (((pat val) . rst)
     `(let ((greatbadness ,val))
	(case-match greatbadness
	  (,pat (let-match* ,rst ,body)))))))

;; ---- Definitions ----

(defdata sender-state `(sendstate ,tl ,nat))

(defdata receiver-state `(recvstate ,tl ,nat))

(defdata ack nat)

(defdata event (enum '(ok drop-ack drop-packet)))
(defdata event-deck (listof event))

;; Sim-state -- (sender-state receiver-state steps)
(defdata sim-state `(sim-state ,sender-state ,receiver-state))

;; ---- Functions ----

(definec simulator-state-check (sim :sim-state) :bool
  (let-match* ((('sim-state sender-state &) sim)
	       (('sendstate data seq-num) sender-state))
    (> (len data) seq-num)))

(definec simulator-step (sim :sim-state event :event) :sim-state
  (if (not (simulator-state-check sim)) sim
    (let-match* ((('sim-state ('sendstate sdata sseq) ('recvstate rdata &)) sim))
      (cond
       ((and (== event 'ok) (== sseq (len rdata)))
	`(sim-state (sendstate ,sdata ,(1+ sseq))
		    (recvstate ,(app rdata (list (nth sseq sdata))) 0)))
       (T sim)))))

(check= (simulator-step '(sim-state (sendstate (1 2) 0) (recvstate nil 0)) 'ok)
	'(sim-state (sendstate (1 2) 1) (recvstate (1) 0)))

(check= (simulator-step '(sim-state (sendstate (1 2) 1) (recvstate (1) 0)) 'ok)
	'(sim-state (sendstate (1 2) 2) (recvstate (1 2) 0)))

;; (check= (simulator-step '(sim-state (sendstate (1) 0) (recvstate () 0)) 'ok)
;; 	'(sim-state (sendstate (1) 1) (recvstate (4 5 6 1) 0) ()))


(skip-proofs
 (definec simulator (sim :sim-state steps :event-deck) :sim-state
   :function-contract-strictp nil
   :body-contracts-strictp nil
   :skip-tests t
   (cond
    ((lendp steps) sim)
    (T (simulator-step (simulator sim (cdr steps)) (car steps))))))

(check= (simulator '(sim-state (sendstate (1 2 3) 0) (recvstate () 0)) '(ok ok ok))
	'(4 5 6 1 2 3))

;; (definec simulator* (data :data steps :event-deck) :data
;;   :function-contract-strictp nil
;;   :ic (>= (len data) (len steps))
;;   (let-match* ((('sim-state & ('recvstate rs &))
;; 		(simulator `(sim-state (sendstate ,data 0) (recvstate nil 0)) steps)))
;;     rs))

;; (check= (simulator* '(4 5 6) '(nil nil nil))
;; 	'(4 5 6))

;; ---- Proofs ----

;; Checks if x is a prefix of y
(definec prefixp (x :tl y :tl) :bool
  (cond
   ((lendp x) T)
   ((lendp y) (lendp x))
   (T (and (equal (car x) (car y))
	   (prefixp (cdr x) (cdr y))))))

;; First confirm test? works
(test? (implies (and (datap d)
		     (event-deckp n)
		     (>= (len d) (len n)))
		(prefixp (simulator* d n) d)))

(defthm prefix-nth
  (implies (and
	    (tlp x)
	    (tlp y)
	    (prefixp x y)
	    (< (len x) (len y))
	    (== index (len x)))
	   (prefixp (app x (list (nth index y))) y)))

(definec rs-prefix-of-ssp (sim :sim-state) :bool
  (let-match* ((('sim-state ('sendstate ss &) ('recvstate rs &)) sim))
    (prefixp rs ss)))

#| == The proof sketch ==

We know receiver state is a prefix of sender state (via C3), and that
the sender sequence number is equal to it's length (via C4). So we should
be able to utilize the prefix-nth lemma to show that the prefix property holds.
|#

(defthm simulator-step-prefix-property
  (implies (and (sim-statep sim)
		(rs-prefix-of-ssp sim)
		(eventp evt))
	   (rs-prefix-of-ssp (simulator-step sim evt)))
  :hints (("Goal" :do-not-induct t
	   :do-not generalize)
	  ("Subgoal 2'5'" :use (:instance prefix-nth
					  (y sim8)
					  (x sim9)
					  (index (len sim9))))))

(skip-proofs
 (defthm simulator-function-contract
   (implies (and (sim-statep sim)
		 (event-deckp evt))
	    (sim-statep (simulator sim evt)))))

(in-theory (disable simulator-step-definition-rule))
(defthm simulator-prefix-property
  (implies (and (sim-statep sim)
		(event-deckp evt)
		(rs-prefix-of-ssp sim))
	   (rs-prefix-of-ssp (simulator sim evt)))
  :hints (("Goal" :induct (simulator sim evt))))
