package view;

import java.util.Arrays;
import java.util.List;
import java.util.Iterator;
import kodkod.ast.*;
import kodkod.ast.operator.*;
import kodkod.instance.*;
import kodkod.engine.*;
import kodkod.engine.satlab.SATFactory;
import kodkod.engine.config.Options;

import java.io.StringReader;
import java.net.URL;
import java.util.*;
import javax.xml.parsers.SAXParser;
import javax.xml.parsers.SAXParserFactory;
import org.xml.sax.Attributes;
import org.xml.sax.SAXException;
import org.xml.sax.helpers.DefaultHandler;
import org.xml.sax.XMLReader;
import org.xml.sax.helpers.XMLReaderFactory;
import org.xml.sax.*;

/* 
  ==================================================
    kodkod formula: 
  ==================================================
    no (this/Choice & this/Parallel) && 
    no ((this/Choice + this/Parallel) & this/Try) && 
    no ((this/Choice + this/Parallel + this/Try) & this/Sequential) && 
    no ((this/Choice + this/Parallel + this/Try + this/Sequential) & this/Leaf) && 
    (all show_this: this/Choice + this/Parallel + this/Try + this/Sequential + 
     this/Leaf | 
      lone (show_this . this/Node.nextSiblingC) && 
      (show_this . this/Node.nextSiblingC) in this/Choice) && 
    (this/Node.nextSiblingC . univ) in (this/Choice + this/Parallel + this/Try + 
    this/Sequential + this/Leaf) && 
    (all show_this: this/Choice + this/Parallel + this/Try + this/Sequential + 
     this/Leaf | 
      lone (show_this . this/Node.firstChildC) && 
      (show_this . this/Node.firstChildC) in this/Choice) && 
    (this/Node.firstChildC . univ) in (this/Choice + this/Parallel + this/Try + 
    this/Sequential + this/Leaf) && 
    no (this/Node.nextSiblingC & this/Node.firstChildC) && 
    (all show_this: this/Choice + this/Parallel + this/Try + this/Sequential + 
     this/Leaf | 
      lone (show_this . this/Node.nextSiblingP) && 
      (show_this . this/Node.nextSiblingP) in this/Parallel) && 
    (this/Node.nextSiblingP . univ) in (this/Choice + this/Parallel + this/Try + 
    this/Sequential + this/Leaf) && 
    (all show_this: this/Choice + this/Parallel + this/Try + this/Sequential + 
     this/Leaf | 
      lone (show_this . this/Node.firstChildP) && 
      (show_this . this/Node.firstChildP) in this/Parallel) && 
    (this/Node.firstChildP . univ) in (this/Choice + this/Parallel + this/Try + 
    this/Sequential + this/Leaf) && 
    no (this/Node.nextSiblingP & this/Node.firstChildP) && 
    (all show_this: this/Choice + this/Parallel + this/Try + this/Sequential + 
     this/Leaf | 
      lone (show_this . this/Node.nextSiblingT) && 
      (show_this . this/Node.nextSiblingT) in this/Try) && 
    (this/Node.nextSiblingT . univ) in (this/Choice + this/Parallel + this/Try + 
    this/Sequential + this/Leaf) && 
    (all show_this: this/Choice + this/Parallel + this/Try + this/Sequential + 
     this/Leaf | 
      lone (show_this . this/Node.firstChildT) && 
      (show_this . this/Node.firstChildT) in this/Try) && 
    (this/Node.firstChildT . univ) in (this/Choice + this/Parallel + this/Try + 
    this/Sequential + this/Leaf) && 
    no (this/Node.nextSiblingT & this/Node.firstChildT) && 
    (all show_this: this/Choice + this/Parallel + this/Try + this/Sequential + 
     this/Leaf | 
      lone (show_this . this/Node.nextSiblingS) && 
      (show_this . this/Node.nextSiblingS) in this/Sequential) && 
    (this/Node.nextSiblingS . univ) in (this/Choice + this/Parallel + this/Try + 
    this/Sequential + this/Leaf) && 
    (all show_this: this/Choice + this/Parallel + this/Try + this/Sequential + 
     this/Leaf | 
      lone (show_this . this/Node.firstChildS) && 
      (show_this . this/Node.firstChildS) in this/Sequential) && 
    (this/Node.firstChildS . univ) in (this/Choice + this/Parallel + this/Try + 
    this/Sequential + this/Leaf) && 
    no (this/Node.nextSiblingS & this/Node.firstChildS) && 
    (all show_this: this/Choice + this/Parallel + this/Try + this/Sequential + 
     this/Leaf | 
      lone (show_this . this/Node.nextSiblingLeaf) && 
      (show_this . this/Node.nextSiblingLeaf) in this/Leaf) && 
    (this/Node.nextSiblingLeaf . univ) in (this/Choice + this/Parallel + 
    this/Try + this/Sequential + this/Leaf) && 
    (all show_this: this/Choice + this/Parallel + this/Try + this/Sequential + 
     this/Leaf | 
      lone (show_this . this/Node.firstChildLeaf) && 
      (show_this . this/Node.firstChildLeaf) in this/Leaf) && 
    (this/Node.firstChildLeaf . univ) in (this/Choice + this/Parallel + this/Try + 
    this/Sequential + this/Leaf) && 
    no (this/Node.nextSiblingLeaf & this/Node.firstChildLeaf) && 
    (all show_this: this/Choice + this/Parallel + this/Try + this/Sequential + 
     this/Leaf | 
      (show_this . this/Node.child) in (this/Choice + this/Parallel + this/Try + 
      this/Sequential + this/Leaf)) && 
    (this/Node.child . univ) in (this/Choice + this/Parallel + this/Try + 
    this/Sequential + this/Leaf) && 
    (all show_this: this/Choice + this/Parallel + this/Try + this/Sequential + 
     this/Leaf | 
      (show_this . this/Node.sibling) in (this/Choice + this/Parallel + this/Try + 
      this/Sequential + this/Leaf)) && 
    (this/Node.sibling . univ) in (this/Choice + this/Parallel + this/Try + 
    this/Sequential + this/Leaf) && 
    (all show_this: this/Choice + this/Parallel + this/Try + this/Sequential + 
     this/Leaf | 
      (show_this . this/Node.subtree) in (this/Choice + this/Parallel + this/Try + 
      this/Sequential + this/Leaf)) && 
    (this/Node.subtree . univ) in (this/Choice + this/Parallel + this/Try + 
    this/Sequential + this/Leaf) && 
    one (this/Process . (this/Process -> this/Process.root)) && 
    (this/Process . (this/Process -> this/Process.root)) in (this/Choice + 
    this/Parallel + this/Try + this/Sequential + this/Leaf) && 
    some (this/Sched . (this/Sched -> this/Sched.header)) && 
    (this/Sched . (this/Sched -> this/Sched.header)) in this/SchedEl && 
    (all show_this: this/SchedEl | 
      (show_this . this/SchedEl.nextEl) in this/SchedEl) && 
    (this/SchedEl.nextEl . univ) in this/SchedEl && 
    (all show_this: this/SchedEl | 
      one (show_this . this/SchedEl.ref) && 
      (show_this . this/SchedEl.ref) in this/Leaf) && 
    (this/SchedEl.ref . univ) in this/SchedEl && 
    (all show_n: this/Choice + this/Parallel + this/Try + this/Sequential + 
     this/Leaf | 
      !(show_n in (show_n . this/Node.subtree))) && 
    (this/Choice + this/Parallel + this/Try + this/Sequential + this/Leaf) = (
    this/Process.root . (^this/Node.subtree + (iden & ((ints + String + 
    this/Choice + this/Parallel + this/Try + this/Sequential + this/Leaf + 
    this/Process + this/Sched + this/SchedEl) -> univ)))) && 
    (all show_n: this/SchedEl | 
      !(show_n in (show_n . ^this/SchedEl.nextEl))) && 
    this/SchedEl = (this/Sched.header . (^this/SchedEl.nextEl + (iden & ((ints + 
    String + this/Choice + this/Parallel + this/Try + this/Sequential + 
    this/Leaf + this/Process + this/Sched + this/SchedEl) -> univ)))) && 
    (all show_t: this/SchedEl, show_t': this/SchedEl | 
      !((show_t . this/SchedEl.ref) = (show_t' . this/SchedEl.ref)) || 
      show_t = show_t') && 
    (all show_n: this/Choice + this/Parallel + this/Try + this/Sequential + 
     this/Leaf | 
      (show_n . this/Node.child) = ((show_n . this/Node.firstChildC) + (show_n . 
      this/Node.firstChildP) + (show_n . this/Node.firstChildT) + (show_n . 
      this/Node.firstChildS) + (show_n . this/Node.firstChildLeaf))) && 
    (all show_n: this/Choice + this/Parallel + this/Try + this/Sequential + 
     this/Leaf | 
      (show_n . this/Node.sibling) = ((show_n . this/Node.nextSiblingC) + (
      show_n . this/Node.nextSiblingP) + (show_n . this/Node.nextSiblingT) + (
      show_n . this/Node.nextSiblingS) + (show_n . this/Node.nextSiblingLeaf))) && 
    (all show_l: this/Leaf | 
      no (show_l . this/Node.subtree)) && 
    (all show_n: this/Choice | 
      (show_n . this/Node.subtree) = (((show_n . this/Node.child) . (^
      this/Node.sibling + (iden & ((ints + String + this/Choice + this/Parallel + 
      this/Try + this/Sequential + this/Leaf + this/Process + this/Sched + 
      this/SchedEl) -> univ)))) + (((show_n . this/Node.child) . (^
      this/Node.sibling + (iden & ((ints + String + this/Choice + this/Parallel + 
      this/Try + this/Sequential + this/Leaf + this/Process + this/Sched + 
      this/SchedEl) -> univ)))) . this/Node.subtree))) && 
    (all show_n: this/Try | 
      (show_n . this/Node.subtree) = (((show_n . this/Node.child) . (^
      this/Node.sibling + (iden & ((ints + String + this/Choice + this/Parallel + 
      this/Try + this/Sequential + this/Leaf + this/Process + this/Sched + 
      this/SchedEl) -> univ)))) + (((show_n . this/Node.child) . (^
      this/Node.sibling + (iden & ((ints + String + this/Choice + this/Parallel + 
      this/Try + this/Sequential + this/Leaf + this/Process + this/Sched + 
      this/SchedEl) -> univ)))) . this/Node.subtree))) && 
    (all show_n: this/Parallel | 
      (show_n . this/Node.subtree) = (((show_n . this/Node.child) . (^
      this/Node.sibling + (iden & ((ints + String + this/Choice + this/Parallel + 
      this/Try + this/Sequential + this/Leaf + this/Process + this/Sched + 
      this/SchedEl) -> univ)))) + (((show_n . this/Node.child) . (^
      this/Node.sibling + (iden & ((ints + String + this/Choice + this/Parallel + 
      this/Try + this/Sequential + this/Leaf + this/Process + this/Sched + 
      this/SchedEl) -> univ)))) . this/Node.subtree))) && 
    (all show_n: this/Sequential | 
      (show_n . this/Node.subtree) = (((show_n . this/Node.child) . (^
      this/Node.sibling + (iden & ((ints + String + this/Choice + this/Parallel + 
      this/Try + this/Sequential + this/Leaf + this/Process + this/Sched + 
      this/SchedEl) -> univ)))) + (((show_n . this/Node.child) . (^
      this/Node.sibling + (iden & ((ints + String + this/Choice + this/Parallel + 
      this/Try + this/Sequential + this/Leaf + this/Process + this/Sched + 
      this/SchedEl) -> univ)))) . this/Node.subtree))) && 
    (all show_n: this/Choice + this/Parallel + this/Try + this/Sequential + 
     this/Leaf, show_n': this/Choice + this/Parallel + this/Try + 
     this/Sequential + this/Leaf | 
      !(no (show_n & show_n') && 
        some ((show_n . this/Node.child) & (show_n' . this/Node.child)))) && 
    (all show_n: this/Choice | 
      #(show_n . this/Node.child) = 1) && 
    (all show_n: this/Try | 
      #(show_n . this/Node.child) = 1) && 
    (all show_n: this/Parallel | 
      #(show_n . this/Node.child) = 1) && 
    (all show_n: this/Sequential | 
      #(show_n . this/Node.child) = 1) && 
    (all show_n: this/Leaf | 
      no (show_n . this/Node.child)) && 
    (all show_n: this/Choice + this/Parallel + this/Try + this/Sequential + 
     this/Leaf | 
      #(show_n . this/Node.sibling) < 2) && 
    (all show_m: this/Choice + this/Parallel + this/Try + this/Sequential + 
     this/Leaf, show_n: this/Choice + this/Parallel + this/Try + this/Sequential + 
     this/Leaf | 
      !(show_m in (show_n . this/Node.subtree)) || 
      !(show_m in (show_n . ^this/Node.sibling))) && 
    (all show_m: this/Choice + this/Parallel + this/Try + this/Sequential + 
     this/Leaf, show_n: this/Choice + this/Parallel + this/Try + this/Sequential + 
     this/Leaf | 
      !(show_m in (show_n . ^this/Node.sibling)) || 
      !(show_m in (show_n . this/Node.subtree))) && 
    (all show_n: this/Choice, show_l: this/Leaf, show_l': this/Leaf | 
      !(show_l in ((show_n . this/Node.child) . (^this/Node.sibling + (iden & ((
        ints + String + this/Choice + this/Parallel + this/Try + this/Sequential + 
        this/Leaf + this/Process + this/Sched + this/SchedEl) -> univ)))) && 
        show_l' in ((show_n . this/Node.child) . (^this/Node.sibling + (iden & (
        (ints + String + this/Choice + this/Parallel + this/Try + 
        this/Sequential + this/Leaf + this/Process + this/Sched + this/SchedEl) -> 
        univ)))) && 
        show_l' in ((this/Sched.header . (^this/SchedEl.nextEl + (iden & ((ints + 
        String + this/Choice + this/Parallel + this/Try + this/Sequential + 
        this/Leaf + this/Process + this/Sched + this/SchedEl) -> univ)))) . 
        this/SchedEl.ref) && 
        show_l in ((this/Sched.header . (^this/SchedEl.nextEl + (iden & ((ints + 
        String + this/Choice + this/Parallel + this/Try + this/Sequential + 
        this/Leaf + this/Process + this/Sched + this/SchedEl) -> univ)))) . 
        this/SchedEl.ref)) || 
      show_l = show_l') && 
    (all show_n: this/Choice, show_m: this/Choice + this/Parallel + this/Try + 
     this/Sequential + this/Leaf, show_m': this/Choice + this/Parallel + 
     this/Try + this/Sequential + this/Leaf, show_l: this/Leaf, show_l': 
     this/Leaf | 
      !(show_m in (show_n . this/Node.subtree) && 
        show_l in (show_m . this/Node.subtree) && 
        show_m' in (show_n . this/Node.subtree) && 
        show_l' in (show_m' . this/Node.subtree) && 
        show_l in ((this/Sched.header . (^this/SchedEl.nextEl + (iden & ((ints + 
        String + this/Choice + this/Parallel + this/Try + this/Sequential + 
        this/Leaf + this/Process + this/Sched + this/SchedEl) -> univ)))) . 
        this/SchedEl.ref) && 
        show_l' in ((this/Sched.header . (^this/SchedEl.nextEl + (iden & ((ints + 
        String + this/Choice + this/Parallel + this/Try + this/Sequential + 
        this/Leaf + this/Process + this/Sched + this/SchedEl) -> univ)))) . 
        this/SchedEl.ref)) || 
      show_m = show_m' || 
      show_m in (show_m' . this/Node.subtree) || 
      show_m' in (show_m . this/Node.subtree)) && 
    (all show_n: this/Try, show_l: this/Leaf, show_l': this/Leaf | 
      !(show_l in ((show_n . this/Node.child) . (^this/Node.sibling + (iden & ((
        ints + String + this/Choice + this/Parallel + this/Try + this/Sequential + 
        this/Leaf + this/Process + this/Sched + this/SchedEl) -> univ)))) && 
        show_l' in ((show_n . this/Node.child) . (^this/Node.sibling + (iden & (
        (ints + String + this/Choice + this/Parallel + this/Try + 
        this/Sequential + this/Leaf + this/Process + this/Sched + this/SchedEl) -> 
        univ)))) && 
        show_l' in ((this/Sched.header . (^this/SchedEl.nextEl + (iden & ((ints + 
        String + this/Choice + this/Parallel + this/Try + this/Sequential + 
        this/Leaf + this/Process + this/Sched + this/SchedEl) -> univ)))) . 
        this/SchedEl.ref) && 
        show_l in ((this/Sched.header . (^this/SchedEl.nextEl + (iden & ((ints + 
        String + this/Choice + this/Parallel + this/Try + this/Sequential + 
        this/Leaf + this/Process + this/Sched + this/SchedEl) -> univ)))) . 
        this/SchedEl.ref)) || 
      show_l = show_l') && 
    (all show_n: this/Try, show_m: this/Choice + this/Parallel + this/Try + 
     this/Sequential + this/Leaf, show_m': this/Choice + this/Parallel + 
     this/Try + this/Sequential + this/Leaf, show_l: this/Leaf, show_l': 
     this/Leaf | 
      !(show_m in (show_n . this/Node.subtree) && 
        show_l in (show_m . this/Node.subtree) && 
        show_m' in (show_n . this/Node.subtree) && 
        show_l' in (show_m' . this/Node.subtree) && 
        show_l in ((this/Sched.header . (^this/SchedEl.nextEl + (iden & ((ints + 
        String + this/Choice + this/Parallel + this/Try + this/Sequential + 
        this/Leaf + this/Process + this/Sched + this/SchedEl) -> univ)))) . 
        this/SchedEl.ref) && 
        show_l' in ((this/Sched.header . (^this/SchedEl.nextEl + (iden & ((ints + 
        String + this/Choice + this/Parallel + this/Try + this/Sequential + 
        this/Leaf + this/Process + this/Sched + this/SchedEl) -> univ)))) . 
        this/SchedEl.ref)) || 
      show_m = show_m' || 
      show_m in (show_m' . this/Node.subtree) || 
      show_m' in (show_m . this/Node.subtree)) && 
    (all show_n: this/Parallel, show_l: this/Leaf | 
      !(show_l in ((show_n . this/Node.child) . (^this/Node.sibling + (iden & ((
        ints + String + this/Choice + this/Parallel + this/Try + this/Sequential + 
        this/Leaf + this/Process + this/Sched + this/SchedEl) -> univ))))) || 
      show_l in ((this/Sched.header . (^this/SchedEl.nextEl + (iden & ((ints + 
      String + this/Choice + this/Parallel + this/Try + this/Sequential + 
      this/Leaf + this/Process + this/Sched + this/SchedEl) -> univ)))) . 
      this/SchedEl.ref)) && 
    (all show_n: this/Sequential, show_l: this/Leaf | 
      !(show_l in ((show_n . this/Node.child) . (^this/Node.sibling + (iden & ((
        ints + String + this/Choice + this/Parallel + this/Try + this/Sequential + 
        this/Leaf + this/Process + this/Sched + this/SchedEl) -> univ))))) || 
      show_l in ((this/Sched.header . (^this/SchedEl.nextEl + (iden & ((ints + 
      String + this/Choice + this/Parallel + this/Try + this/Sequential + 
      this/Leaf + this/Process + this/Sched + this/SchedEl) -> univ)))) . 
      this/SchedEl.ref)) && 
    (all show_n: this/Parallel, show_l: this/Leaf, show_l': this/Leaf, show_s: 
     this/SchedEl, show_s': this/SchedEl | 
      !(show_l in ((show_n . this/Node.child) . (^this/Node.sibling + (iden & ((
        ints + String + this/Choice + this/Parallel + this/Try + this/Sequential + 
        this/Leaf + this/Process + this/Sched + this/SchedEl) -> univ)))) && 
        show_l' in ((show_n . this/Node.child) . (^this/Node.sibling + (iden & (
        (ints + String + this/Choice + this/Parallel + this/Try + 
        this/Sequential + this/Leaf + this/Process + this/Sched + this/SchedEl) -> 
        univ)))) && 
        show_l' in (show_s' . this/SchedEl.ref) && 
        show_s in this/Sched.header && 
        show_l in (show_s . this/SchedEl.ref)) || 
      show_s' in this/Sched.header) && 
    (all show_n: this/Parallel, show_p: this/Choice + this/Parallel + this/Try + 
     this/Sequential + this/Leaf, show_q: this/Choice + this/Parallel + this/Try + 
     this/Sequential + this/Leaf, show_l: this/Leaf, show_l': this/Leaf, show_s: 
     this/SchedEl, show_s': this/SchedEl | 
      !(show_p in (show_n + (show_n . this/Node.subtree)) && 
        show_q in (show_n + (show_n . this/Node.subtree)) && 
        (show_l' in (show_q . this/Node.child) || 
         show_l' in ((show_n . this/Node.child) . (^this/Node.sibling + (iden & 
         ((ints + String + this/Choice + this/Parallel + this/Try + 
         this/Sequential + this/Leaf + this/Process + this/Sched + this/SchedEl) -> 
         univ))))) && 
        show_l in (show_s . this/SchedEl.ref) && 
        (show_l in (show_p . this/Node.child) || 
         show_l in ((show_n . this/Node.child) . (^this/Node.sibling + (iden & (
         (ints + String + this/Choice + this/Parallel + this/Try + 
         this/Sequential + this/Leaf + this/Process + this/Sched + this/SchedEl) -> 
         univ))))) && 
        show_l' in (show_s' . this/SchedEl.ref) && 
        show_s in this/Sched.header) || 
      show_s' in this/Sched.header) && 
    (all show_n: this/Parallel, show_p: this/Choice + this/Parallel + this/Try + 
     this/Sequential + this/Leaf, show_q: this/Choice + this/Parallel + this/Try + 
     this/Sequential + this/Leaf, show_l: this/Leaf, show_l': this/Leaf, show_s: 
     this/SchedEl, show_s': this/SchedEl, show_f: this/SchedEl | 
      !(show_p in (show_n + (show_n . this/Node.subtree)) && 
        show_q in (show_n + (show_n . this/Node.subtree)) && 
        (show_l' in (show_q . this/Node.child) || 
         show_l' in ((show_n . this/Node.child) . (^this/Node.sibling + (iden & 
         ((ints + String + this/Choice + this/Parallel + this/Try + 
         this/Sequential + this/Leaf + this/Process + this/Sched + this/SchedEl) -> 
         univ))))) && 
        show_l in (show_s . this/SchedEl.ref) && 
        (show_l in (show_p . this/Node.child) || 
         show_l in ((show_n . this/Node.child) . (^this/Node.sibling + (iden & (
         (ints + String + this/Choice + this/Parallel + this/Try + 
         this/Sequential + this/Leaf + this/Process + this/Sched + this/SchedEl) -> 
         univ))))) && 
        show_l' in (show_s' . this/SchedEl.ref) && 
        show_s in (show_f . this/SchedEl.nextEl)) || 
      show_s' in (show_f . this/SchedEl.nextEl)) && 
    (all show_l: this/Leaf, show_l': this/Leaf | 
      !(show_l in (this/Sched.header . this/SchedEl.ref) && 
        show_l' in (this/Sched.header . this/SchedEl.ref) && 
        !(show_l = show_l')) || 
      (show_l in (this/Parallel . this/Node.subtree) && 
       show_l' in (this/Parallel . this/Node.subtree))) && 
    (all show_s: this/SchedEl, show_s': this/SchedEl | 
      !(show_s in this/Sched.header && 
        show_s' in (show_s . ^this/SchedEl.nextEl)) || 
      !(show_s' in this/Sched.header)) && 
    (all show_l: this/Leaf, show_l': this/Leaf, show_p: this/SchedEl | 
      !(show_l in ((show_p . this/SchedEl.nextEl) . this/SchedEl.ref) && 
        show_l' in ((show_p . this/SchedEl.nextEl) . this/SchedEl.ref) && 
        !(show_l = show_l')) || 
      (show_l in (this/Parallel . this/Node.subtree) && 
       show_l' in (this/Parallel . this/Node.subtree))) && 
    (all show_n: this/Sequential, show_p: this/Choice + this/Parallel + this/Try + 
     this/Sequential + this/Leaf, show_q: this/Choice + this/Parallel + this/Try + 
     this/Sequential + this/Leaf, show_l: this/Leaf, show_l': this/Leaf, show_s: 
     this/SchedEl, show_s': this/SchedEl | 
      !(show_p in ((show_n . this/Node.child) . (^this/Node.sibling + (iden & ((
        ints + String + this/Choice + this/Parallel + this/Try + this/Sequential + 
        this/Leaf + this/Process + this/Sched + this/SchedEl) -> univ)))) && 
        show_q in (show_p . ^this/Node.sibling) && 
        show_l' in (show_q . this/Node.subtree) && 
        show_l in (show_s . this/SchedEl.ref) && 
        show_l in (show_p . this/Node.subtree) && 
        show_l' in (show_s' . this/SchedEl.ref)) || 
      show_s' in (show_s . ^this/SchedEl.nextEl)) && 
    Int/next = Int/next && 
    seq/Int = seq/Int && 
    String = String && 
    this/Choice = this/Choice && 
    this/Parallel = this/Parallel && 
    this/Try = this/Try && 
    this/Sequential = this/Sequential && 
    this/Leaf = this/Leaf && 
    this/Process = this/Process && 
    this/Sched = this/Sched && 
    this/SchedEl = this/SchedEl && 
    this/Node.nextSiblingC = this/Node.nextSiblingC && 
    this/Node.firstChildC = this/Node.firstChildC && 
    this/Node.nextSiblingP = this/Node.nextSiblingP && 
    this/Node.firstChildP = this/Node.firstChildP && 
    this/Node.nextSiblingT = this/Node.nextSiblingT && 
    this/Node.firstChildT = this/Node.firstChildT && 
    this/Node.nextSiblingS = this/Node.nextSiblingS && 
    this/Node.firstChildS = this/Node.firstChildS && 
    this/Node.nextSiblingLeaf = this/Node.nextSiblingLeaf && 
    this/Node.firstChildLeaf = this/Node.firstChildLeaf && 
    this/Node.child = this/Node.child && 
    this/Node.sibling = this/Node.sibling && 
    this/Node.subtree = this/Node.subtree && 
    this/Process.root = this/Process.root && 
    this/Sched.header = this/Sched.header && 
    this/SchedEl.nextEl = this/SchedEl.nextEl && 
    this/SchedEl.ref = this/SchedEl.ref
  ==================================================
 */

public final class tmp1086813879216744668 {
	/* booleans to keep track of what XML tag was just read */
	boolean stepdecl;
	boolean connector;
	boolean subconnector;
	//	protected String parentNode;
	/* my implementation of linked list nodes for a process */
	public ProcessNode root,currParent,currSibling;
	ProcessNode[] allNodes = null; //used to quickly access a stored node using an index
	int numNodes; //total number of process nodes read in from XML file
	static int s, p, c, t, l; //counters for how many of each type of node we parse in

	public class ProcessNode{
		String type,nodeName; //type=XML tag, nodeName=Kodkod label
		ProcessNode parent, nextSibling, firstChild; //pointers used for tree implementation
		public ProcessNode(){ //empty constructor
			type="";
			nodeName="";
		}
		public ProcessNode(String type){ //type=XML tag
			this.type=type;
			/* Generate a unique Kodkod label using node counters */
			if(type.equalsIgnoreCase("sequential")){
				nodeName="Sequential$".concat(Integer.toString(tmp1086813879216744668.s));
				tmp1086813879216744668.s++;
			}
			if(type.equalsIgnoreCase("parallel")){
				nodeName="Parallel$".concat(Integer.toString(tmp1086813879216744668.p));
				tmp1086813879216744668.p++;
			}
			if(type.equalsIgnoreCase("try")){
				nodeName="Try$".concat(Integer.toString(tmp1086813879216744668.t));
				tmp1086813879216744668.t++;
			}
			if(type.equalsIgnoreCase("choice")){
				nodeName="Choice$".concat(Integer.toString(tmp1086813879216744668.c));
				tmp1086813879216744668.c++;
			}
			if(type.equalsIgnoreCase("leaf")){
				nodeName="Leaf$".concat(Integer.toString(tmp1086813879216744668.l));
				tmp1086813879216744668.l++;
			}
		}

		public String toString(){
			return nodeName;
		}

		/*Print all reachable nodeNames using preorder traversal */
		public void printTree(String prefix){
			System.out.println(prefix+nodeName);
			if(firstChild!=null)firstChild.printTree(prefix.concat("\t"));
			if(nextSibling!=null)nextSibling.printTree(prefix);
		}

		/* Aggregate all reachable nodeNames into a list */
		public List<String> getAllSubNodeNames(){
			List<String> l = new LinkedList<String>();
			l.add(nodeName);
			if(firstChild!=null)l.addAll(firstChild.getAllSubNodeNames());
			if(nextSibling!=null)l.addAll(nextSibling.getAllSubNodeNames());
			return l;
		}

		/* Aggregate all reachable node objects into a list */
		public ArrayList<ProcessNode> getClosure(){
			ArrayList<ProcessNode> closure = new ArrayList<ProcessNode>();
			if(firstChild!=null) closure.addAll(firstChild.getClosure());
			if(nextSibling!=null) closure.addAll(nextSibling.getClosure());
			closure.add(this);
			return closure;
		}

		/* Assigns unique node names but overwrites names given during parsing */
		public void nameSubNodes(){
			if(type.equalsIgnoreCase("sequential")){
				nodeName="Sequential$".concat(Integer.toString(tmp1086813879216744668.s));
				tmp1086813879216744668.s++;
			}
			if(type.equalsIgnoreCase("parallel")){
				nodeName="Parallel$".concat(Integer.toString(tmp1086813879216744668.p));
				tmp1086813879216744668.p++;
			}
			if(type.equalsIgnoreCase("try")){
				nodeName="Try$".concat(Integer.toString(tmp1086813879216744668.t));
				tmp1086813879216744668.t++;
			}
			if(type.equalsIgnoreCase("choice")){
				nodeName="Choice$".concat(Integer.toString(tmp1086813879216744668.c));
				tmp1086813879216744668.c++;
			}
			if(type.equalsIgnoreCase("leaf")){
				nodeName="Leaf$".concat(Integer.toString(tmp1086813879216744668.l));
				tmp1086813879216744668.l++;
			}
			if(firstChild!=null) firstChild.nameSubNodes();
			if(nextSibling!=null) nextSibling.nameSubNodes();
		}
	}

	/* Quickly access a particular node in the process tree */
	public ProcessNode getNode(int index){
		if(allNodes==null && root != null){
			allNodes=root.getClosure().toArray(new ProcessNode[root.getClosure().size()]);
		}
		if(allNodes.length>index){
			return allNodes[index];
		}
		return null;
	}

	/* This class gets rid of an XML parsing error since the DTD file is no longer available */
	public class DummyEntityResolver implements EntityResolver {
		public DummyEntityResolver(){}
		public InputSource resolveEntity(String publicID, String systemID)
				throws SAXException {

			return new InputSource(new StringReader(""));
		}
	}

	public tmp1086813879216744668(){
		numNodes=0;
		stepdecl=false;
		connector=false;
		subconnector=false;
		//		parentNode="";
		/* Initialize counters storing how many of each type of node has been parsed */
		tmp1086813879216744668.s=0;
		tmp1086813879216744668.p=0;
		tmp1086813879216744668.t=0;
		tmp1086813879216744668.l=0;
		try {
			SAXParserFactory factory = SAXParserFactory.newInstance();
			factory.setValidating(false); 
			SAXParser saxParser = factory.newSAXParser();

			DefaultHandler handler = new DefaultHandler() {		
				public void startElement(String uri, String localName,String qName, 
						Attributes attributes) throws SAXException {
					//System.out.println("Start Element :" + qName);

					if (qName.equalsIgnoreCase("STEP-DECLARATION")) {
						//create a new process node
						stepdecl = true;
						numNodes++;
						if(root==null){
							root = new ProcessNode(attributes.getValue(1)); //index 1 in tag stores the type
							//System.out.println("\tNew root: "+root);
						}
						else{
							ProcessNode n = new ProcessNode(attributes.getValue(1));
							n.parent=currParent;
							if(currParent==null) System.out.println("ERROR: creating multiple root nodes!");
							if(currSibling==null){
								currSibling=n;
								currParent.firstChild=n;
								//System.out.println("\tAdded "+n+" as first child under parent "+currParent);
							}
							else{
								currSibling.nextSibling=n;
								//System.out.println("\tAdded "+n+" as sibling of "+currSibling+" under parent "+currParent);
								currSibling=n;
							}
						}
					}

					if (qName.equalsIgnoreCase("CONNECTOR")) {
						//move down a level
						connector = true;
						if(currParent==null){
							currParent=root;
						}
						else{
							currParent=currSibling;
							currSibling=currParent.firstChild;
							while(currSibling != null && currSibling.nextSibling != null){
								currSibling=currSibling.nextSibling;
							}
							if(currParent==null) System.out.println("ERROR: failed to move down a level");
						}
						//System.out.println("\tMoving down a level, parent is now "+currParent);
					}

					if (qName.equalsIgnoreCase("SUBSTEP-CONNECTOR")) {
						//do nothing
						subconnector = true;
					}
				}

				public void endElement(String uri, String localName,
						String qName) throws SAXException {
					System.out.println("End Element :" + qName);
					if (qName.equalsIgnoreCase("STEP-DECLARATION")) {
						//do nothing, should be taken care of in opening tag
					}

					if (qName.equalsIgnoreCase("CONNECTOR")) {
						//move up a level
						subconnector = true;
						if(currParent==null){
							System.out.println("ERROR: could not move up a level, nowhere to go");
						}
						else{
							currParent=currParent.parent;
							if(currParent!=null){
								currSibling=currParent.firstChild;
								while(currSibling != null && currSibling.nextSibling != null){
									currSibling=currSibling.nextSibling;
								}
							}
						}
						//System.out.println("\tMoving up a level, parent is now "+currParent);
					}

					if (qName.equalsIgnoreCase("SUBSTEP-CONNECTOR")) {
						//do nothing, this is an empty tag in little jil
					}
				}

				public void characters(char ch[], int start, int length) throws SAXException {

					if (stepdecl) {
						System.out.println("Node");
						stepdecl = false;
					}

					if (connector) {
						System.out.println("Connector");
						connector = false;
					}

					if (subconnector) {
						System.out.println("Sub Connector");
						subconnector = false;
					}
				}	 
			};
			XMLReader xmlreader = XMLReaderFactory.createXMLReader();
			//xmlreader.setFeature("http://laser.cs.umass.edu/dtd/littlejil-1.5.dtd", false);
			xmlreader.setEntityResolver(new DummyEntityResolver());
			xmlreader.setContentHandler(handler);
			xmlreader.parse("Module1.ljx");
			//saxParser.parse("Module1.ljx", handler);
			//if(root!=null) root.nameSubNodes();
		} catch (Exception e) {
			e.printStackTrace();
		}
	}

	public static void main(String[] args) throws Exception {
		tmp1086813879216744668 t = new tmp1086813879216744668();		
		t.root.printTree("");

		Relation x0 = Relation.nary("Int/next", 2);
		Relation x1 = Relation.unary("seq/Int");
		Relation x2 = Relation.unary("String");
		Relation x3 = Relation.unary("this/C");
		Relation x4 = Relation.unary("this/P");
		Relation x5 = Relation.unary("this/T");
		Relation x6 = Relation.unary("this/S");
		Relation x7 = Relation.unary("this/L1");
		Relation x8 = Relation.unary("this/L2");
		Relation x9 = Relation.unary("this/L3");
		Relation x10 = Relation.unary("this/L4");
		Relation x11 = Relation.unary("this/L5");
		Relation x12 = Relation.unary("this/L6");
		Relation x13 = Relation.unary("this/L7");
		Relation x14 = Relation.unary("this/Process");
		Relation x15 = Relation.unary("this/Sched");
		Relation x16 = Relation.unary("this/SchedEl");
		Relation x17 = Relation.nary("this/Node.nextSiblingC", 2);
		Relation x18 = Relation.nary("this/Node.firstChildC", 2);
		Relation x19 = Relation.nary("this/Node.nextSiblingP", 2);
		Relation x20 = Relation.nary("this/Node.firstChildP", 2);
		Relation x21 = Relation.nary("this/Node.nextSiblingT", 2);
		Relation x22 = Relation.nary("this/Node.firstChildT", 2);
		Relation x23 = Relation.nary("this/Node.nextSiblingS", 2);
		Relation x24 = Relation.nary("this/Node.firstChildS", 2);
		Relation x25 = Relation.nary("this/Node.nextSiblingLeaf", 2);
		Relation x26 = Relation.nary("this/Node.firstChildLeaf", 2);
		Relation x27 = Relation.nary("this/Node.child", 2);
		Relation x28 = Relation.nary("this/Node.sibling", 2);
		Relation x29 = Relation.nary("this/Node.subtree", 2);
		Relation x30 = Relation.unary("this/Process.root");
		Relation x31 = Relation.unary("this/Sched.header");
		Relation x32 = Relation.nary("this/SchedEl.nextEl", 2);
		Relation x33 = Relation.nary("this/SchedEl.ref", 2);

		//TODO replace all uses of x_ objects to use relations[index]
		Relation[] relations = new Relation[3+t.numNodes+20];
		int relationIndex=0;
		relations[relationIndex++]=Relation.nary("Int/next", 2);
		relations[relationIndex++]=Relation.unary("seq/Int");
		relations[relationIndex++] = Relation.unary("String");
		int relationNodeStart=relationIndex; //remember index where relations for our parsed nodes start
		for(int i=0; i<t.numNodes; i++){
			relations[relationIndex++] = Relation.unary("this/"+t.getNode(i).nodeName);
		}
		relations[relationIndex++] =  Relation.unary("this/Process");
		relations[relationIndex++] = Relation.unary("this/Sched");
		relations[relationIndex++] = Relation.unary("this/SchedEl");
		relations[relationIndex++] = Relation.nary("this/Node.nextSiblingC", 2);
		relations[relationIndex++] = Relation.nary("this/Node.firstChildC", 2);
		relations[relationIndex++] = Relation.nary("this/Node.nextSiblingP", 2);
		relations[relationIndex++] = Relation.nary("this/Node.firstChildP", 2);
		relations[relationIndex++] = Relation.nary("this/Node.nextSiblingT", 2);
		relations[relationIndex++] = Relation.nary("this/Node.firstChildT", 2);
		relations[relationIndex++] = Relation.nary("this/Node.nextSiblingS", 2);
		relations[relationIndex++] =  Relation.nary("this/Node.firstChildS", 2);
		relations[relationIndex++] =  Relation.nary("this/Node.nextSiblingLeaf", 2);
		relations[relationIndex++] = Relation.nary("this/Node.firstChildLeaf", 2);
		relations[relationIndex++] = Relation.nary("this/Node.child", 2);
		relations[relationIndex++] = Relation.nary("this/Node.sibling", 2);
		relations[relationIndex++] =  Relation.nary("this/Node.subtree", 2);
		relations[relationIndex++] = Relation.unary("this/Process.root");
		relations[relationIndex++] = Relation.unary("this/Sched.header");
		relations[relationIndex++] = Relation.nary("this/SchedEl.nextEl", 2);
		relations[relationIndex++] = Relation.nary("this/SchedEl.ref", 2);

		List<String> atomlist = Arrays.asList(
				"C$0", "L1$0", "L2$0", "L3$0", "L4$0",
				"L5$0", "L6$0", "L7$0", "P$0", "Process$0", "S$0",
				"Sched$0", "SchedEl$0", "SchedEl$1", "SchedEl$2", "SchedEl$3", "SchedEl$4",
				"SchedEl$5", "SchedEl$6", "T$0"
				);

		List<String> nodelist = t.root.getAllSubNodeNames();
		nodelist.add("Process$0");
		nodelist.add("Sched$0");
		for (int i=0;i<t.l; i++){ //Upper bound for SchedEl is total number of leaves
			nodelist.add("SchedEl$"+Integer.toString(i));
		}
		Universe universe = new Universe(atomlist);
		//TODO use this:
		//Universe universe = new Universe(nodelist);
		TupleFactory factory = universe.factory();
		Bounds bounds = new Bounds(universe);

		//TODO replace all uses of x_upper objects with use of x.get(index)
		List<TupleSet> x = new ArrayList<TupleSet>();

		TupleSet x0_upper = factory.noneOf(2);
		bounds.boundExactly(x0, x0_upper); //relation Int/next
		x.add(x0_upper);

		TupleSet x1_upper = factory.noneOf(1);
		bounds.boundExactly(x1, x1_upper); //relation set/Int
		x.add(x1_upper);

		TupleSet x2_upper = factory.noneOf(1);
		bounds.boundExactly(x2, x2_upper); //relation String
		x.add(x2_upper);

		TupleSet x3_upper = factory.noneOf(1);
		x3_upper.add(factory.tuple("C$0"));
		bounds.boundExactly(x3, x3_upper); //relation this/C

		TupleSet x4_upper = factory.noneOf(1);
		x4_upper.add(factory.tuple("P$0"));
		bounds.boundExactly(x4, x4_upper); //relation this/P

		TupleSet x5_upper = factory.noneOf(1);
		x5_upper.add(factory.tuple("T$0"));
		bounds.boundExactly(x5, x5_upper); //x5 is relation this/T

		TupleSet x6_upper = factory.noneOf(1);
		x6_upper.add(factory.tuple("S$0"));
		bounds.boundExactly(x6, x6_upper); //relation this/S

		TupleSet x7_upper = factory.noneOf(1);
		x7_upper.add(factory.tuple("L1$0"));
		bounds.boundExactly(x7, x7_upper); //relation this/L1

		TupleSet x8_upper = factory.noneOf(1);
		x8_upper.add(factory.tuple("L2$0"));
		bounds.boundExactly(x8, x8_upper); //relation this/L2

		TupleSet x9_upper = factory.noneOf(1);
		x9_upper.add(factory.tuple("L3$0"));
		bounds.boundExactly(x9, x9_upper); //relation this/L3

		TupleSet x10_upper = factory.noneOf(1);
		x10_upper.add(factory.tuple("L4$0"));
		bounds.boundExactly(x10, x10_upper); //relation this/L4

		TupleSet x11_upper = factory.noneOf(1);
		x11_upper.add(factory.tuple("L5$0"));
		bounds.boundExactly(x11, x11_upper); //relation this/L5

		TupleSet x12_upper = factory.noneOf(1);
		x12_upper.add(factory.tuple("L6$0"));
		bounds.boundExactly(x12, x12_upper); //relation this/L6

		TupleSet x13_upper = factory.noneOf(1);
		x13_upper.add(factory.tuple("L7$0"));
		bounds.boundExactly(x13, x13_upper); //relation this/L7

		for (int i=0; i<t.numNodes; i++){ //bundles all this/C, this/P, this/L1-L7, etc together by going through our stored tree
			TupleSet temp = factory.noneOf(1);
			//temp.add(factory.tuple(t.getNode(i).nodeName));
			bounds.boundExactly(relations[relationNodeStart+i], temp);
			x.add(temp);
		}

		TupleSet x14_upper = factory.noneOf(1);
		x14_upper.add(factory.tuple("Process$0"));
		bounds.boundExactly(x14, x14_upper); //x14 is relation this/Process
		x.add(x14_upper);

		TupleSet x15_upper = factory.noneOf(1);
		x15_upper.add(factory.tuple("Sched$0"));
		bounds.boundExactly(x15, x15_upper); //x15 is relation this/Sched
		x.add(x15_upper);

		TupleSet x16_upper = factory.noneOf(1);
		for(int i = 0; i < 7; i++)
			x16_upper.add(factory.tuple("SchedEl$" + i));
		bounds.bound(x16, x16_upper); //x16 is relation this/SchedEl

		TupleSet temp = factory.noneOf(1);
		for(int i=0; i<t.l; i++){
			temp.add(factory.tuple("SchedEl$"+Integer.toString(i)));
		}
		//bounds.bound(relations[relationNodeStart+t.numNodes+3], temp);//TODO double check index


		//TODO
		/*
		 * dot product of all nodes with all C nodes twice (for nextSibling and for firstChild)
		 */
		TupleSet x17_upper = factory.noneOf(2);
		x17_upper.add(factory.tuple("C$0").product(factory.tuple("C$0")));
		x17_upper.add(factory.tuple("P$0").product(factory.tuple("C$0")));
		x17_upper.add(factory.tuple("T$0").product(factory.tuple("C$0")));
		x17_upper.add(factory.tuple("S$0").product(factory.tuple("C$0")));
		for(int i=1; i<8 ;i++){
			x17_upper.add(factory.tuple("L"+i+"$0").product(factory.tuple("C$0")));
		}
		bounds.bound(x17, x17_upper); //relation this/Node.nextSiblingC

		TupleSet x18_upper = factory.noneOf(2);
		x18_upper.add(factory.tuple("C$0").product(factory.tuple("C$0")));
		x18_upper.add(factory.tuple("P$0").product(factory.tuple("C$0")));
		x18_upper.add(factory.tuple("T$0").product(factory.tuple("C$0")));
		x18_upper.add(factory.tuple("S$0").product(factory.tuple("C$0")));
		for(int i=1; i<8 ;i++){
			x18_upper.add(factory.tuple("L"+i+"$0").product(factory.tuple("C$0")));
		}
		bounds.bound(x18, x18_upper); //relation this/Node.firstChildC

		//TODO
		/*
		 * dot product of all nodes with all P nodes twice (for nextSibling and for firstChild)
		 */
		TupleSet x19_upper = factory.noneOf(2);
		x19_upper.add(factory.tuple("C$0").product(factory.tuple("P$0")));
		x19_upper.add(factory.tuple("P$0").product(factory.tuple("P$0")));
		x19_upper.add(factory.tuple("T$0").product(factory.tuple("P$0")));
		x19_upper.add(factory.tuple("S$0").product(factory.tuple("P$0")));
		for(int i=1; i<8 ;i++){
			x19_upper.add(factory.tuple("L"+i+"$0").product(factory.tuple("P$0")));
		}
		bounds.bound(x19, x19_upper); //relation this/Node.nextSiblingP

		TupleSet x20_upper = factory.noneOf(2);
		x20_upper.add(factory.tuple("C$0").product(factory.tuple("P$0")));
		x20_upper.add(factory.tuple("P$0").product(factory.tuple("P$0")));
		x20_upper.add(factory.tuple("T$0").product(factory.tuple("P$0")));
		x20_upper.add(factory.tuple("S$0").product(factory.tuple("P$0")));
		for(int i=1; i<8 ;i++){
			x20_upper.add(factory.tuple("L"+i+"$0").product(factory.tuple("P$0")));
		}
		bounds.bound(x20, x20_upper); //relation this/Node.firstChildP

		//TODO
		/*
		 * dot product of all nodes with all T nodes twice (for nextSibling and for firstChild)
		 */
		TupleSet x21_upper = factory.noneOf(2);
		x21_upper.add(factory.tuple("C$0").product(factory.tuple("T$0")));
		x21_upper.add(factory.tuple("P$0").product(factory.tuple("T$0")));
		x21_upper.add(factory.tuple("T$0").product(factory.tuple("T$0")));
		x21_upper.add(factory.tuple("S$0").product(factory.tuple("T$0")));
		for(int i=1; i<8 ;i++){
			x21_upper.add(factory.tuple("L"+i+"$0").product(factory.tuple("T$0")));
		}
		
		bounds.bound(x21, x21_upper); //relation this/Node.nextSiblingT

		TupleSet x22_upper = factory.noneOf(2);
		x22_upper.add(factory.tuple("C$0").product(factory.tuple("T$0")));
		x22_upper.add(factory.tuple("P$0").product(factory.tuple("T$0")));
		x22_upper.add(factory.tuple("T$0").product(factory.tuple("T$0")));
		x22_upper.add(factory.tuple("S$0").product(factory.tuple("T$0")));
		for(int i=1; i<8 ;i++){
			x22_upper.add(factory.tuple("L"+i+"$0").product(factory.tuple("T$0")));
		}
		bounds.bound(x22, x22_upper); //relation this/Node.firstChildT

		//TODO
		/*
		 * dot product of all nodes with all S nodes twice (for nextSibling and for firstChild)
		 */

		TupleSet x23_upper = factory.noneOf(2);
		x23_upper.add(factory.tuple("C$0").product(factory.tuple("S$0")));
		x23_upper.add(factory.tuple("P$0").product(factory.tuple("S$0")));
		x23_upper.add(factory.tuple("T$0").product(factory.tuple("S$0")));
		x23_upper.add(factory.tuple("S$0").product(factory.tuple("S$0")));
		for(int i=1; i<8 ;i++){
			x23_upper.add(factory.tuple("L"+i+"$0").product(factory.tuple("S$0")));
		}
		bounds.bound(x23, x23_upper); //relation this/Node.nextSiblingS

		TupleSet x24_upper = factory.noneOf(2);
		x24_upper.add(factory.tuple("C$0").product(factory.tuple("S$0")));
		x24_upper.add(factory.tuple("P$0").product(factory.tuple("S$0")));
		x24_upper.add(factory.tuple("T$0").product(factory.tuple("S$0")));
		x24_upper.add(factory.tuple("S$0").product(factory.tuple("S$0")));
		for(int i=1; i<8 ;i++){
			x24_upper.add(factory.tuple("L"+i+"$0").product(factory.tuple("S$0")));
		}
		bounds.bound(x24, x24_upper); //relation this/Node.firstChildS

		//TODO
		/*
		 * dot product of all nodes with all Leaf nodes twice (for nextSibling and for firstChild)
		 */
		TupleSet x25_upper = factory.noneOf(2);
		for(int i=1; i<8 ;i++){
			x25_upper.add(factory.tuple("C$0").product(factory.tuple("L"+i+"$0")));
		}
		for(int i=1; i<8 ;i++){
			x25_upper.add(factory.tuple("P$0").product(factory.tuple("L"+i+"$0")));
		}
		for(int i=1; i<8 ;i++){
			x25_upper.add(factory.tuple("T$0").product(factory.tuple("L"+i+"$0")));
		}
		for(int i=1; i<8 ;i++){
			x25_upper.add(factory.tuple("S$0").product(factory.tuple("L"+i+"$0")));
		}
		
		for(int i=1; i<8; i++){
			for(int j=1; j<8 ;j++){
				x25_upper.add(factory.tuple("L"+i+"$0").product(factory.tuple("L"+j+"$0")));
			}
		}
		
		bounds.bound(x25, x25_upper); //relation this/Node.nextSiblingLeaf

		TupleSet x26_upper = factory.noneOf(2);
		
		for(int i=1; i<8 ;i++){
			x26_upper.add(factory.tuple("C$0").product(factory.tuple("L"+i+"$0")));
		}
		for(int i=1; i<8 ;i++){
			x26_upper.add(factory.tuple("P$0").product(factory.tuple("L"+i+"$0")));
		}
		for(int i=1; i<8 ;i++){
			x26_upper.add(factory.tuple("T$0").product(factory.tuple("L"+i+"$0")));
		}
		for(int i=1; i<8 ;i++){
			x26_upper.add(factory.tuple("S$0").product(factory.tuple("L"+i+"$0")));
		}
		
		for(int i=1; i<8; i++){
			for(int j=1; j<8 ;j++){
				x26_upper.add(factory.tuple("L"+i+"$0").product(factory.tuple("L"+j+"$0")));
			}
		}
		
		bounds.bound(x26, x26_upper); //relation this/Node.firstChildLeaf

		//TODO
		/*
		 * dot product of all nodes with all nodes thrice (for child, sibling and subtree)
		 */

		TupleSet x27_upper = factory.noneOf(2);
		
		x27_upper.add(factory.tuple("C$0").product(factory.tuple("C$0")));
		x27_upper.add(factory.tuple("C$0").product(factory.tuple("P$0")));
		x27_upper.add(factory.tuple("C$0").product(factory.tuple("T$0")));
		x27_upper.add(factory.tuple("C$0").product(factory.tuple("S$0")));
		for(int i=1;i<8;i++){
			x27_upper.add(factory.tuple("C$0").product(factory.tuple("L"+i+"$0")));
		}
		
		x27_upper.add(factory.tuple("P$0").product(factory.tuple("C$0")));
		x27_upper.add(factory.tuple("P$0").product(factory.tuple("P$0")));
		x27_upper.add(factory.tuple("P$0").product(factory.tuple("T$0")));
		x27_upper.add(factory.tuple("P$0").product(factory.tuple("S$0")));
		for(int i=1;i<8;i++){
			x27_upper.add(factory.tuple("P$0").product(factory.tuple("L"+i+"$0")));
		}
		x27_upper.add(factory.tuple("T$0").product(factory.tuple("C$0")));
		x27_upper.add(factory.tuple("T$0").product(factory.tuple("P$0")));
		x27_upper.add(factory.tuple("T$0").product(factory.tuple("T$0")));
		x27_upper.add(factory.tuple("T$0").product(factory.tuple("S$0")));
		for(int i=1;i<8;i++){
			x27_upper.add(factory.tuple("T$0").product(factory.tuple("L"+i+"$0")));
		}
		
		x27_upper.add(factory.tuple("S$0").product(factory.tuple("C$0")));
		x27_upper.add(factory.tuple("S$0").product(factory.tuple("P$0")));
		x27_upper.add(factory.tuple("S$0").product(factory.tuple("T$0")));
		x27_upper.add(factory.tuple("S$0").product(factory.tuple("S$0")));

		for(int i=1;i<8;i++){
			x27_upper.add(factory.tuple("S$0").product(factory.tuple("L"+i+"$0")));
		}
		
		for(int i=1; i<8; i++){
			for (int j=1; j<8; j++){
				x27_upper.add(factory.tuple("L"+i+"$0").product(factory.tuple("C$0")));
				x27_upper.add(factory.tuple("L"+i+"$0").product(factory.tuple("P$0")));
				x27_upper.add(factory.tuple("L"+i+"$0").product(factory.tuple("T$0")));
				x27_upper.add(factory.tuple("L"+i+"$0").product(factory.tuple("S$0")));
				x27_upper.add(factory.tuple("L"+i+"$0").product(factory.tuple("L"+j+"$0")));
			}
		}
		
		bounds.bound(x27, x27_upper); //relation this/Node.child

		TupleSet x28_upper = factory.noneOf(2);
		x28_upper.add(factory.tuple("C$0").product(factory.tuple("C$0")));
		x28_upper.add(factory.tuple("C$0").product(factory.tuple("P$0")));
		x28_upper.add(factory.tuple("C$0").product(factory.tuple("T$0")));
		x28_upper.add(factory.tuple("C$0").product(factory.tuple("S$0")));
		for(int i=1;i<8;i++){
			x28_upper.add(factory.tuple("C$0").product(factory.tuple("L"+i+"$0")));
		}
		
		x28_upper.add(factory.tuple("P$0").product(factory.tuple("C$0")));
		x28_upper.add(factory.tuple("P$0").product(factory.tuple("P$0")));
		x28_upper.add(factory.tuple("P$0").product(factory.tuple("T$0")));
		x28_upper.add(factory.tuple("P$0").product(factory.tuple("S$0")));
		for(int i=1;i<8;i++){
			x28_upper.add(factory.tuple("P$0").product(factory.tuple("L"+i+"$0")));
		}
		x28_upper.add(factory.tuple("T$0").product(factory.tuple("C$0")));
		x28_upper.add(factory.tuple("T$0").product(factory.tuple("P$0")));
		x28_upper.add(factory.tuple("T$0").product(factory.tuple("T$0")));
		x28_upper.add(factory.tuple("T$0").product(factory.tuple("S$0")));
		for(int i=1;i<8;i++){
			x28_upper.add(factory.tuple("T$0").product(factory.tuple("L"+i+"$0")));
		}
		
		x28_upper.add(factory.tuple("S$0").product(factory.tuple("C$0")));
		x28_upper.add(factory.tuple("S$0").product(factory.tuple("P$0")));
		x28_upper.add(factory.tuple("S$0").product(factory.tuple("T$0")));
		x28_upper.add(factory.tuple("S$0").product(factory.tuple("S$0")));

		for(int i=1;i<8;i++){
			x28_upper.add(factory.tuple("S$0").product(factory.tuple("L"+i+"$0")));
		}
		
		for(int i=1; i<8; i++){
			for (int j=1; j<8; j++){
				x28_upper.add(factory.tuple("L"+i+"$0").product(factory.tuple("C$0")));
				x28_upper.add(factory.tuple("L"+i+"$0").product(factory.tuple("P$0")));
				x28_upper.add(factory.tuple("L"+i+"$0").product(factory.tuple("T$0")));
				x28_upper.add(factory.tuple("L"+i+"$0").product(factory.tuple("S$0")));
				x28_upper.add(factory.tuple("L"+i+"$0").product(factory.tuple("L"+j+"$0")));
			}
		}
		
		bounds.bound(x28, x28_upper); //relation this/Node.child

		TupleSet x29_upper = factory.noneOf(2);
		
		x29_upper.add(factory.tuple("C$0").product(factory.tuple("C$0")));
		x29_upper.add(factory.tuple("C$0").product(factory.tuple("P$0")));
		x29_upper.add(factory.tuple("C$0").product(factory.tuple("T$0")));
		x29_upper.add(factory.tuple("C$0").product(factory.tuple("S$0")));
		for(int i=1;i<8;i++){
			x29_upper.add(factory.tuple("C$0").product(factory.tuple("L"+i+"$0")));
		}
		
		x29_upper.add(factory.tuple("P$0").product(factory.tuple("C$0")));
		x29_upper.add(factory.tuple("P$0").product(factory.tuple("P$0")));
		x29_upper.add(factory.tuple("P$0").product(factory.tuple("T$0")));
		x29_upper.add(factory.tuple("P$0").product(factory.tuple("S$0")));
		for(int i=1;i<8;i++){
			x29_upper.add(factory.tuple("P$0").product(factory.tuple("L"+i+"$0")));
		}
		x29_upper.add(factory.tuple("T$0").product(factory.tuple("C$0")));
		x29_upper.add(factory.tuple("T$0").product(factory.tuple("P$0")));
		x29_upper.add(factory.tuple("T$0").product(factory.tuple("T$0")));
		x29_upper.add(factory.tuple("T$0").product(factory.tuple("S$0")));
		for(int i=1;i<8;i++){
			x29_upper.add(factory.tuple("T$0").product(factory.tuple("L"+i+"$0")));
		}
		
		x29_upper.add(factory.tuple("S$0").product(factory.tuple("C$0")));
		x29_upper.add(factory.tuple("S$0").product(factory.tuple("P$0")));
		x29_upper.add(factory.tuple("S$0").product(factory.tuple("T$0")));
		x29_upper.add(factory.tuple("S$0").product(factory.tuple("S$0")));

		for(int i=1;i<8;i++){
			x29_upper.add(factory.tuple("S$0").product(factory.tuple("L"+i+"$0")));
		}
		
		for(int i=1; i<8; i++){
			for (int j=1; j<8; j++){
				x29_upper.add(factory.tuple("L"+i+"$0").product(factory.tuple("C$0")));
				x29_upper.add(factory.tuple("L"+i+"$0").product(factory.tuple("P$0")));
				x29_upper.add(factory.tuple("L"+i+"$0").product(factory.tuple("T$0")));
				x29_upper.add(factory.tuple("L"+i+"$0").product(factory.tuple("S$0")));
				x29_upper.add(factory.tuple("L"+i+"$0").product(factory.tuple("L"+j+"$0")));
			}
		}
		
		bounds.bound(x29, x29_upper); //relation this/Node.subtree

		//TODO
		/*
		 * x.add(factory.tuple(all nodes))
		 */
		TupleSet x30_upper = factory.noneOf(1);
		x30_upper.add(factory.tuple("C$0"));
		x30_upper.add(factory.tuple("P$0"));
		x30_upper.add(factory.tuple("T$0"));
		x30_upper.add(factory.tuple("S$0"));
		for (int i = 1; i < 8; i++)
			x30_upper.add(factory.tuple("L" + i + "$0"));
		bounds.bound(x30, x30_upper); //relation this/Process.root

		//TODO
		/*
		 * x.add(factory.tuple(all SchedEls))
		 */
		TupleSet x31_upper = factory.noneOf(1);
		for (int i = 0; i < 7; i++)
			x31_upper.add(factory.tuple("SchedEl$" + i));
		bounds.bound(x31, x31_upper); //relation this/Sched.header

		//TODO
		/*
		 * dot product of all SchedEl with all SchedEl (for nextEl)
		 */
		TupleSet x32_upper = factory.noneOf(2);
		for(int i = 0; i < 7; i++)
			for(int j = 0; i < 7; i++)
				x32_upper.add(factory.tuple("SchedEl$" + i).product(factory.tuple("SchedEl$" + j)));
		bounds.bound(x32, x32_upper); //relation this/SchedEl.nextEl

		//TODO
		/*
		 * dot product of all SchedEl with all Leaf nodes (for SchedEl.ref)
		 */
		TupleSet x33_upper = factory.noneOf(2);
		for(int i = 0; i < 7; i++)
			for(int j = 1; j < 8; j++)
					x33_upper.add(factory.tuple("SchedEl$"+i).product(factory.tuple("L"+j+"$0")));
		
		bounds.bound(x33, x33_upper); //relation this/SchedEl.ref


		Expression x36=x3.intersection(x4);
		Formula x35=x36.no();
		Expression x39=x3.union(x4);
		Expression x38=x39.intersection(x5);
		Formula x37=x38.no();
		Expression x42=x39.union(x5);
		Expression x41=x42.intersection(x6);
		Formula x40=x41.no();
		Expression x44=x7.intersection(x8);
		Formula x43=x44.no();
		Expression x47=x7.union(x8);
		Expression x46=x47.intersection(x9);
		Formula x45=x46.no();
		Expression x50=x47.union(x9);
		Expression x49=x50.intersection(x10);
		Formula x48=x49.no();
		Expression x53=x50.union(x10);
		Expression x52=x53.intersection(x11);
		Formula x51=x52.no();
		Expression x56=x53.union(x11);
		Expression x55=x56.intersection(x12);
		Formula x54=x55.no();
		Expression x59=x56.union(x12);
		Expression x58=x59.intersection(x13);
		Formula x57=x58.no();
		Expression x62=x42.union(x6);
		Expression x63=x59.union(x13);
		Expression x61=x62.intersection(x63);
		Formula x60=x61.no();
		Variable x66=Variable.unary("show_this");
		Expression x67=x62.union(x63);
		Decls x65=x66.oneOf(x67);
		Expression x70=x66.join(x17);
		Formula x69=x70.lone();
		Formula x71=x70.in(x3);
		Formula x68=x69.and(x71);
		Formula x64=x68.forAll(x65);
		Expression x73=x17.join(Expression.UNIV);
		Formula x72=x73.in(x67);
		Variable x77=Variable.unary("show_this");
		Decls x76=x77.oneOf(x67);
		Expression x80=x77.join(x18);
		Formula x79=x80.lone();
		Formula x81=x80.in(x3);
		Formula x78=x79.and(x81);
		Formula x75=x78.forAll(x76);
		Expression x83=x18.join(Expression.UNIV);
		Formula x82=x83.in(x67);
		Expression x85=x17.intersection(x18);
		Formula x84=x85.no();
		Variable x88=Variable.unary("show_this");
		Decls x87=x88.oneOf(x67);
		Expression x91=x88.join(x19);
		Formula x90=x91.lone();
		Formula x92=x91.in(x4);
		Formula x89=x90.and(x92);
		Formula x86=x89.forAll(x87);
		Expression x94=x19.join(Expression.UNIV);
		Formula x93=x94.in(x67);
		Variable x97=Variable.unary("show_this");
		Decls x96=x97.oneOf(x67);
		Expression x100=x97.join(x20);
		Formula x99=x100.lone();
		Formula x101=x100.in(x4);
		Formula x98=x99.and(x101);
		Formula x95=x98.forAll(x96);
		Expression x103=x20.join(Expression.UNIV);
		Formula x102=x103.in(x67);
		Expression x105=x19.intersection(x20);
		Formula x104=x105.no();
		Variable x108=Variable.unary("show_this");
		Decls x107=x108.oneOf(x67);
		Expression x111=x108.join(x21);
		Formula x110=x111.lone();
		Formula x112=x111.in(x5);
		Formula x109=x110.and(x112);
		Formula x106=x109.forAll(x107);
		Expression x114=x21.join(Expression.UNIV);
		Formula x113=x114.in(x67);
		Variable x117=Variable.unary("show_this");
		Decls x116=x117.oneOf(x67);
		Expression x120=x117.join(x22);
		Formula x119=x120.lone();
		Formula x121=x120.in(x5);
		Formula x118=x119.and(x121);
		Formula x115=x118.forAll(x116);
		Expression x123=x22.join(Expression.UNIV);
		Formula x122=x123.in(x67);
		Expression x125=x21.intersection(x22);
		Formula x124=x125.no();
		Variable x128=Variable.unary("show_this");
		Decls x127=x128.oneOf(x67);
		Expression x131=x128.join(x23);
		Formula x130=x131.lone();
		Formula x132=x131.in(x6);
		Formula x129=x130.and(x132);
		Formula x126=x129.forAll(x127);
		Expression x134=x23.join(Expression.UNIV);
		Formula x133=x134.in(x67);
		Variable x137=Variable.unary("show_this");
		Decls x136=x137.oneOf(x67);
		Expression x140=x137.join(x24);
		Formula x139=x140.lone();
		Formula x141=x140.in(x6);
		Formula x138=x139.and(x141);
		Formula x135=x138.forAll(x136);
		Expression x143=x24.join(Expression.UNIV);
		Formula x142=x143.in(x67);
		Expression x145=x23.intersection(x24);
		Formula x144=x145.no();
		Variable x148=Variable.unary("show_this");
		Decls x147=x148.oneOf(x67);
		Expression x151=x148.join(x25);
		Formula x150=x151.lone();
		Formula x152=x151.in(x63);
		Formula x149=x150.and(x152);
		Formula x146=x149.forAll(x147);
		Expression x154=x25.join(Expression.UNIV);
		Formula x153=x154.in(x67);
		Variable x157=Variable.unary("show_this");
		Decls x156=x157.oneOf(x67);
		Expression x160=x157.join(x26);
		Formula x159=x160.lone();
		Formula x161=x160.in(x63);
		Formula x158=x159.and(x161);
		Formula x155=x158.forAll(x156);
		Expression x163=x26.join(Expression.UNIV);
		Formula x162=x163.in(x67);
		Expression x165=x25.intersection(x26);
		Formula x164=x165.no();
		Variable x168=Variable.unary("show_this");
		Decls x167=x168.oneOf(x67);
		Expression x170=x168.join(x27);
		Formula x169=x170.in(x67);
		Formula x166=x169.forAll(x167);
		Expression x172=x27.join(Expression.UNIV);
		Formula x171=x172.in(x67);
		Variable x175=Variable.unary("show_this");
		Decls x174=x175.oneOf(x67);
		Expression x177=x175.join(x28);
		Formula x176=x177.in(x67);
		Formula x173=x176.forAll(x174);
		Expression x179=x28.join(Expression.UNIV);
		Formula x178=x179.in(x67);
		Variable x182=Variable.unary("show_this");
		Decls x181=x182.oneOf(x67);
		Expression x184=x182.join(x29);
		Formula x183=x184.in(x67);
		Formula x180=x183.forAll(x181);
		Expression x186=x29.join(Expression.UNIV);
		Formula x185=x186.in(x67);
		Expression x190=x14.product(x30);
		Expression x189=x14.join(x190);
		Formula x188=x189.one();
		Formula x191=x189.in(x67);
		Formula x187=x188.and(x191);
		Expression x195=x15.product(x31);
		Expression x194=x15.join(x195);
		Formula x193=x194.some();
		Formula x196=x194.in(x16);
		Formula x192=x193.and(x196);
		Variable x199=Variable.unary("show_this");
		Decls x198=x199.oneOf(x16);
		Expression x201=x199.join(x32);
		Formula x200=x201.in(x16);
		Formula x197=x200.forAll(x198);
		Expression x203=x32.join(Expression.UNIV);
		Formula x202=x203.in(x16);
		Variable x206=Variable.unary("show_this");
		Decls x205=x206.oneOf(x16);
		Expression x209=x206.join(x33);
		Formula x208=x209.one();
		Formula x210=x209.in(x63);
		Formula x207=x208.and(x210);
		Formula x204=x207.forAll(x205);
		Expression x212=x33.join(Expression.UNIV);
		Formula x211=x212.in(x16);
		Variable x215=Variable.unary("show_n");
		Decls x214=x215.oneOf(x67);
		Expression x218=x215.join(x29);
		Formula x217=x215.in(x218);
		Formula x216=x217.not();
		Formula x213=x216.forAll(x214);
		Expression x222=x29.closure();
		Expression x230=Expression.INTS.union(x2);
		Expression x229=x230.union(x67);
		Expression x228=x229.union(x14);
		Expression x227=x228.union(x15);
		Expression x226=x227.union(x16);
		Expression x225=x226.product(Expression.UNIV);
		Expression x223=Expression.IDEN.intersection(x225);
		Expression x221=x222.union(x223);
		Expression x220=x30.join(x221);
		Formula x219=x67.eq(x220);
		Variable x234=Variable.unary("show_n");
		Decls x233=x234.oneOf(x16);
		Expression x238=x32.closure();
		Expression x237=x234.join(x238);
		Formula x236=x234.in(x237);
		Formula x235=x236.not();
		Formula x232=x235.forAll(x233);
		Expression x242=x32.closure();
		Expression x244=x226.product(Expression.UNIV);
		Expression x243=Expression.IDEN.intersection(x244);
		Expression x241=x242.union(x243);
		Expression x240=x31.join(x241);
		Formula x239=x16.eq(x240);
		Variable x248=Variable.unary("show_t");
		Decls x247=x248.oneOf(x16);
		Variable x250=Variable.unary("show_t'");
		Decls x249=x250.oneOf(x16);
		Decls x246=x247.and(x249);
		Expression x254=x248.join(x33);
		Expression x255=x250.join(x33);
		Formula x253=x254.eq(x255);
		Formula x252=x253.not();
		Formula x256=x248.eq(x250);
		Formula x251=x252.or(x256);
		Formula x245=x251.forAll(x246);
		Variable x259=Variable.unary("show_n");
		Decls x258=x259.oneOf(x67);
		Expression x261=x259.join(x27);
		Expression x266=x259.join(x18);
		Expression x267=x259.join(x20);
		Expression x265=x266.union(x267);
		Expression x268=x259.join(x22);
		Expression x264=x265.union(x268);
		Expression x269=x259.join(x24);
		Expression x263=x264.union(x269);
		Expression x270=x259.join(x26);
		Expression x262=x263.union(x270);
		Formula x260=x261.eq(x262);
		Formula x257=x260.forAll(x258);
		Variable x273=Variable.unary("show_n");
		Decls x272=x273.oneOf(x67);
		Expression x275=x273.join(x28);
		Expression x280=x273.join(x17);
		Expression x281=x273.join(x19);
		Expression x279=x280.union(x281);
		Expression x282=x273.join(x21);
		Expression x278=x279.union(x282);
		Expression x283=x273.join(x23);
		Expression x277=x278.union(x283);
		Expression x284=x273.join(x25);
		Expression x276=x277.union(x284);
		Formula x274=x275.eq(x276);
		Formula x271=x274.forAll(x272);
		Variable x287=Variable.unary("show_l");
		Decls x286=x287.oneOf(x63);
		Expression x289=x287.join(x29);
		Formula x288=x289.no();
		Formula x285=x288.forAll(x286);
		Variable x292=Variable.unary("show_n");
		Decls x291=x292.oneOf(x3);
		Expression x294=x292.join(x29);
		Expression x297=x292.join(x27);
		Expression x299=x28.closure();
		Expression x301=x226.product(Expression.UNIV);
		Expression x300=Expression.IDEN.intersection(x301);
		Expression x298=x299.union(x300);
		Expression x296=x297.join(x298);
		Expression x304=x292.join(x27);
		Expression x306=x28.closure();
		Expression x308=x226.product(Expression.UNIV);
		Expression x307=Expression.IDEN.intersection(x308);
		Expression x305=x306.union(x307);
		Expression x303=x304.join(x305);
		Expression x302=x303.join(x29);
		Expression x295=x296.union(x302);
		Formula x293=x294.eq(x295);
		Formula x290=x293.forAll(x291);
		Variable x311=Variable.unary("show_n");
		Decls x310=x311.oneOf(x5);
		Expression x313=x311.join(x29);
		Expression x316=x311.join(x27);
		Expression x318=x28.closure();
		Expression x320=x226.product(Expression.UNIV);
		Expression x319=Expression.IDEN.intersection(x320);
		Expression x317=x318.union(x319);
		Expression x315=x316.join(x317);
		Expression x323=x311.join(x27);
		Expression x325=x28.closure();
		Expression x327=x226.product(Expression.UNIV);
		Expression x326=Expression.IDEN.intersection(x327);
		Expression x324=x325.union(x326);
		Expression x322=x323.join(x324);
		Expression x321=x322.join(x29);
		Expression x314=x315.union(x321);
		Formula x312=x313.eq(x314);
		Formula x309=x312.forAll(x310);
		Variable x330=Variable.unary("show_n");
		Decls x329=x330.oneOf(x4);
		Expression x332=x330.join(x29);
		Expression x335=x330.join(x27);
		Expression x337=x28.closure();
		Expression x339=x226.product(Expression.UNIV);
		Expression x338=Expression.IDEN.intersection(x339);
		Expression x336=x337.union(x338);
		Expression x334=x335.join(x336);
		Expression x342=x330.join(x27);
		Expression x344=x28.closure();
		Expression x346=x226.product(Expression.UNIV);
		Expression x345=Expression.IDEN.intersection(x346);
		Expression x343=x344.union(x345);
		Expression x341=x342.join(x343);
		Expression x340=x341.join(x29);
		Expression x333=x334.union(x340);
		Formula x331=x332.eq(x333);
		Formula x328=x331.forAll(x329);
		Variable x349=Variable.unary("show_n");
		Decls x348=x349.oneOf(x6);
		Expression x351=x349.join(x29);
		Expression x354=x349.join(x27);
		Expression x356=x28.closure();
		Expression x358=x226.product(Expression.UNIV);
		Expression x357=Expression.IDEN.intersection(x358);
		Expression x355=x356.union(x357);
		Expression x353=x354.join(x355);
		Expression x361=x349.join(x27);
		Expression x363=x28.closure();
		Expression x365=x226.product(Expression.UNIV);
		Expression x364=Expression.IDEN.intersection(x365);
		Expression x362=x363.union(x364);
		Expression x360=x361.join(x362);
		Expression x359=x360.join(x29);
		Expression x352=x353.union(x359);
		Formula x350=x351.eq(x352);
		Formula x347=x350.forAll(x348);
		Variable x369=Variable.unary("show_n");
		Decls x368=x369.oneOf(x67);
		Variable x371=Variable.unary("show_n'");
		Decls x370=x371.oneOf(x67);
		Decls x367=x368.and(x370);
		Expression x375=x369.intersection(x371);
		Formula x374=x375.no();
		Expression x378=x369.join(x27);
		Expression x379=x371.join(x27);
		Expression x377=x378.intersection(x379);
		Formula x376=x377.some();
		Formula x373=x374.and(x376);
		Formula x372=x373.not();
		Formula x366=x372.forAll(x367);
		Variable x382=Variable.unary("show_n");
		Decls x381=x382.oneOf(x3);
		Expression x385=x382.join(x27);
		IntExpression x384=x385.count();
		IntExpression x386=IntConstant.constant(1);
		Formula x383=x384.eq(x386);
		Formula x380=x383.forAll(x381);
		Variable x389=Variable.unary("show_n");
		Decls x388=x389.oneOf(x5);
		Expression x392=x389.join(x27);
		IntExpression x391=x392.count();
		IntExpression x393=IntConstant.constant(1);
		Formula x390=x391.eq(x393);
		Formula x387=x390.forAll(x388);
		Variable x396=Variable.unary("show_n");
		Decls x395=x396.oneOf(x4);
		Expression x399=x396.join(x27);
		IntExpression x398=x399.count();
		IntExpression x400=IntConstant.constant(1);
		Formula x397=x398.eq(x400);
		Formula x394=x397.forAll(x395);
		Variable x403=Variable.unary("show_n");
		Decls x402=x403.oneOf(x6);
		Expression x406=x403.join(x27);
		IntExpression x405=x406.count();
		IntExpression x407=IntConstant.constant(1);
		Formula x404=x405.eq(x407);
		Formula x401=x404.forAll(x402);
		Variable x410=Variable.unary("show_n");
		Decls x409=x410.oneOf(x63);
		Expression x412=x410.join(x27);
		Formula x411=x412.no();
		Formula x408=x411.forAll(x409);
		Variable x415=Variable.unary("show_n");
		Decls x414=x415.oneOf(x67);
		Expression x418=x415.join(x28);
		IntExpression x417=x418.count();
		IntExpression x419=IntConstant.constant(2);
		Formula x416=x417.lt(x419);
		Formula x413=x416.forAll(x414);
		Variable x423=Variable.unary("show_m");
		Decls x422=x423.oneOf(x67);
		Variable x425=Variable.unary("show_n");
		Decls x424=x425.oneOf(x67);
		Decls x421=x422.and(x424);
		Expression x429=x425.join(x29);
		Formula x428=x423.in(x429);
		Formula x427=x428.not();
		Expression x433=x28.closure();
		Expression x432=x425.join(x433);
		Formula x431=x423.in(x432);
		Formula x430=x431.not();
		Formula x426=x427.or(x430);
		Formula x420=x426.forAll(x421);
		Variable x437=Variable.unary("show_m");
		Decls x436=x437.oneOf(x67);
		Variable x439=Variable.unary("show_n");
		Decls x438=x439.oneOf(x67);
		Decls x435=x436.and(x438);
		Expression x444=x28.closure();
		Expression x443=x439.join(x444);
		Formula x442=x437.in(x443);
		Formula x441=x442.not();
		Expression x447=x439.join(x29);
		Formula x446=x437.in(x447);
		Formula x445=x446.not();
		Formula x440=x441.or(x445);
		Formula x434=x440.forAll(x435);
		Variable x451=Variable.unary("show_n");
		Decls x450=x451.oneOf(x3);
		Variable x453=Variable.unary("show_l");
		Decls x452=x453.oneOf(x63);
		Variable x455=Variable.unary("show_l'");
		Decls x454=x455.oneOf(x63);
		Decls x449=x450.and(x452).and(x454);
		Expression x462=x451.join(x27);
		Expression x464=x28.closure();
		Expression x466=x226.product(Expression.UNIV);
		Expression x465=Expression.IDEN.intersection(x466);
		Expression x463=x464.union(x465);
		Expression x461=x462.join(x463);
		Formula x460=x453.in(x461);
		Expression x470=x451.join(x27);
		Expression x472=x28.closure();
		Expression x474=x226.product(Expression.UNIV);
		Expression x473=Expression.IDEN.intersection(x474);
		Expression x471=x472.union(x473);
		Expression x469=x470.join(x471);
		Formula x468=x455.in(x469);
		Expression x479=x32.closure();
		Expression x481=x226.product(Expression.UNIV);
		Expression x480=Expression.IDEN.intersection(x481);
		Expression x478=x479.union(x480);
		Expression x477=x31.join(x478);
		Expression x476=x477.join(x33);
		Formula x475=x455.in(x476);
		Formula x467=x468.and(x475);
		Formula x459=x460.and(x467);
		Expression x486=x32.closure();
		Expression x488=x226.product(Expression.UNIV);
		Expression x487=Expression.IDEN.intersection(x488);
		Expression x485=x486.union(x487);
		Expression x484=x31.join(x485);
		Expression x483=x484.join(x33);
		Formula x482=x453.in(x483);
		Formula x458=x459.and(x482);
		Formula x457=x458.not();
		Formula x489=x453.eq(x455);
		Formula x456=x457.or(x489);
		Formula x448=x456.forAll(x449);
		Variable x493=Variable.unary("show_n");
		Decls x492=x493.oneOf(x3);
		Variable x495=Variable.unary("show_m");
		Decls x494=x495.oneOf(x67);
		Variable x497=Variable.unary("show_m'");
		Decls x496=x497.oneOf(x67);
		Variable x499=Variable.unary("show_l");
		Decls x498=x499.oneOf(x63);
		Variable x501=Variable.unary("show_l'");
		Decls x500=x501.oneOf(x63);
		Decls x491=x492.and(x494).and(x496).and(x498).and(x500);
		Expression x507=x493.join(x29);
		Formula x506=x495.in(x507);
		Expression x511=x495.join(x29);
		Formula x510=x499.in(x511);
		Expression x513=x493.join(x29);
		Formula x512=x497.in(x513);
		Formula x509=x510.and(x512);
		Expression x515=x497.join(x29);
		Formula x514=x501.in(x515);
		Formula x508=x509.and(x514);
		Formula x505=x506.and(x508);
		Expression x521=x32.closure();
		Expression x523=x226.product(Expression.UNIV);
		Expression x522=Expression.IDEN.intersection(x523);
		Expression x520=x521.union(x522);
		Expression x519=x31.join(x520);
		Expression x518=x519.join(x33);
		Formula x517=x499.in(x518);
		Expression x528=x32.closure();
		Expression x530=x226.product(Expression.UNIV);
		Expression x529=Expression.IDEN.intersection(x530);
		Expression x527=x528.union(x529);
		Expression x526=x31.join(x527);
		Expression x525=x526.join(x33);
		Formula x524=x501.in(x525);
		Formula x516=x517.and(x524);
		Formula x504=x505.and(x516);
		Formula x503=x504.not();
		Formula x533=x495.eq(x497);
		Expression x535=x497.join(x29);
		Formula x534=x495.in(x535);
		Formula x532=x533.or(x534);
		Expression x537=x495.join(x29);
		Formula x536=x497.in(x537);
		Formula x531=x532.or(x536);
		Formula x502=x503.or(x531);
		Formula x490=x502.forAll(x491);
		Variable x541=Variable.unary("show_n");
		Decls x540=x541.oneOf(x5);
		Variable x543=Variable.unary("show_l");
		Decls x542=x543.oneOf(x63);
		Variable x545=Variable.unary("show_l'");
		Decls x544=x545.oneOf(x63);
		Decls x539=x540.and(x542).and(x544);
		Expression x552=x541.join(x27);
		Expression x554=x28.closure();
		Expression x556=x226.product(Expression.UNIV);
		Expression x555=Expression.IDEN.intersection(x556);
		Expression x553=x554.union(x555);
		Expression x551=x552.join(x553);
		Formula x550=x543.in(x551);
		Expression x560=x541.join(x27);
		Expression x562=x28.closure();
		Expression x564=x226.product(Expression.UNIV);
		Expression x563=Expression.IDEN.intersection(x564);
		Expression x561=x562.union(x563);
		Expression x559=x560.join(x561);
		Formula x558=x545.in(x559);
		Expression x569=x32.closure();
		Expression x571=x226.product(Expression.UNIV);
		Expression x570=Expression.IDEN.intersection(x571);
		Expression x568=x569.union(x570);
		Expression x567=x31.join(x568);
		Expression x566=x567.join(x33);
		Formula x565=x545.in(x566);
		Formula x557=x558.and(x565);
		Formula x549=x550.and(x557);
		Expression x576=x32.closure();
		Expression x578=x226.product(Expression.UNIV);
		Expression x577=Expression.IDEN.intersection(x578);
		Expression x575=x576.union(x577);
		Expression x574=x31.join(x575);
		Expression x573=x574.join(x33);
		Formula x572=x543.in(x573);
		Formula x548=x549.and(x572);
		Formula x547=x548.not();
		Formula x579=x543.eq(x545);
		Formula x546=x547.or(x579);
		Formula x538=x546.forAll(x539);
		Variable x583=Variable.unary("show_n");
		Decls x582=x583.oneOf(x5);
		Variable x585=Variable.unary("show_m");
		Decls x584=x585.oneOf(x67);
		Variable x587=Variable.unary("show_m'");
		Decls x586=x587.oneOf(x67);
		Variable x589=Variable.unary("show_l");
		Decls x588=x589.oneOf(x63);
		Variable x591=Variable.unary("show_l'");
		Decls x590=x591.oneOf(x63);
		Decls x581=x582.and(x584).and(x586).and(x588).and(x590);
		Expression x597=x583.join(x29);
		Formula x596=x585.in(x597);
		Expression x601=x585.join(x29);
		Formula x600=x589.in(x601);
		Expression x603=x583.join(x29);
		Formula x602=x587.in(x603);
		Formula x599=x600.and(x602);
		Expression x605=x587.join(x29);
		Formula x604=x591.in(x605);
		Formula x598=x599.and(x604);
		Formula x595=x596.and(x598);
		Expression x611=x32.closure();
		Expression x613=x226.product(Expression.UNIV);
		Expression x612=Expression.IDEN.intersection(x613);
		Expression x610=x611.union(x612);
		Expression x609=x31.join(x610);
		Expression x608=x609.join(x33);
		Formula x607=x589.in(x608);
		Expression x618=x32.closure();
		Expression x620=x226.product(Expression.UNIV);
		Expression x619=Expression.IDEN.intersection(x620);
		Expression x617=x618.union(x619);
		Expression x616=x31.join(x617);
		Expression x615=x616.join(x33);
		Formula x614=x591.in(x615);
		Formula x606=x607.and(x614);
		Formula x594=x595.and(x606);
		Formula x593=x594.not();
		Formula x623=x585.eq(x587);
		Expression x625=x587.join(x29);
		Formula x624=x585.in(x625);
		Formula x622=x623.or(x624);
		Expression x627=x585.join(x29);
		Formula x626=x587.in(x627);
		Formula x621=x622.or(x626);
		Formula x592=x593.or(x621);
		Formula x580=x592.forAll(x581);
		Variable x631=Variable.unary("show_n");
		Decls x630=x631.oneOf(x4);
		Variable x633=Variable.unary("show_l");
		Decls x632=x633.oneOf(x63);
		Decls x629=x630.and(x632);
		Expression x638=x631.join(x27);
		Expression x640=x28.closure();
		Expression x642=x226.product(Expression.UNIV);
		Expression x641=Expression.IDEN.intersection(x642);
		Expression x639=x640.union(x641);
		Expression x637=x638.join(x639);
		Formula x636=x633.in(x637);
		Formula x635=x636.not();
		Expression x647=x32.closure();
		Expression x649=x226.product(Expression.UNIV);
		Expression x648=Expression.IDEN.intersection(x649);
		Expression x646=x647.union(x648);
		Expression x645=x31.join(x646);
		Expression x644=x645.join(x33);
		Formula x643=x633.in(x644);
		Formula x634=x635.or(x643);
		Formula x628=x634.forAll(x629);
		Variable x653=Variable.unary("show_n");
		Decls x652=x653.oneOf(x6);
		Variable x655=Variable.unary("show_l");
		Decls x654=x655.oneOf(x63);
		Decls x651=x652.and(x654);
		Expression x660=x653.join(x27);
		Expression x662=x28.closure();
		Expression x664=x226.product(Expression.UNIV);
		Expression x663=Expression.IDEN.intersection(x664);
		Expression x661=x662.union(x663);
		Expression x659=x660.join(x661);
		Formula x658=x655.in(x659);
		Formula x657=x658.not();
		Expression x669=x32.closure();
		Expression x671=x226.product(Expression.UNIV);
		Expression x670=Expression.IDEN.intersection(x671);
		Expression x668=x669.union(x670);
		Expression x667=x31.join(x668);
		Expression x666=x667.join(x33);
		Formula x665=x655.in(x666);
		Formula x656=x657.or(x665);
		Formula x650=x656.forAll(x651);
		Variable x675=Variable.unary("show_n");
		Decls x674=x675.oneOf(x4);
		Variable x677=Variable.unary("show_l");
		Decls x676=x677.oneOf(x63);
		Variable x679=Variable.unary("show_l'");
		Decls x678=x679.oneOf(x63);
		Variable x681=Variable.unary("show_s");
		Decls x680=x681.oneOf(x16);
		Variable x683=Variable.unary("show_s'");
		Decls x682=x683.oneOf(x16);
		Decls x673=x674.and(x676).and(x678).and(x680).and(x682);
		Expression x690=x675.join(x27);
		Expression x692=x28.closure();
		Expression x694=x226.product(Expression.UNIV);
		Expression x693=Expression.IDEN.intersection(x694);
		Expression x691=x692.union(x693);
		Expression x689=x690.join(x691);
		Formula x688=x677.in(x689);
		Expression x699=x675.join(x27);
		Expression x701=x28.closure();
		Expression x703=x226.product(Expression.UNIV);
		Expression x702=Expression.IDEN.intersection(x703);
		Expression x700=x701.union(x702);
		Expression x698=x699.join(x700);
		Formula x697=x679.in(x698);
		Expression x705=x683.join(x33);
		Formula x704=x679.in(x705);
		Formula x696=x697.and(x704);
		Formula x706=x681.in(x31);
		Formula x695=x696.and(x706);
		Formula x687=x688.and(x695);
		Expression x708=x681.join(x33);
		Formula x707=x677.in(x708);
		Formula x686=x687.and(x707);
		Formula x685=x686.not();
		Formula x709=x683.in(x31);
		Formula x684=x685.or(x709);
		Formula x672=x684.forAll(x673);
		Variable x713=Variable.unary("show_n");
		Decls x712=x713.oneOf(x4);
		Variable x715=Variable.unary("show_p");
		Decls x714=x715.oneOf(x67);
		Variable x717=Variable.unary("show_q");
		Decls x716=x717.oneOf(x67);
		Variable x719=Variable.unary("show_l");
		Decls x718=x719.oneOf(x63);
		Variable x721=Variable.unary("show_l'");
		Decls x720=x721.oneOf(x63);
		Variable x723=Variable.unary("show_s");
		Decls x722=x723.oneOf(x16);
		Variable x725=Variable.unary("show_s'");
		Decls x724=x725.oneOf(x16);
		Decls x711=x712.and(x714).and(x716).and(x718).and(x720).and(x722).and(x724);
		Expression x732=x713.join(x29);
		Expression x731=x713.union(x732);
		Formula x730=x715.in(x731);
		Expression x737=x713.join(x29);
		Expression x736=x713.union(x737);
		Formula x735=x717.in(x736);
		Expression x740=x717.join(x27);
		Formula x739=x721.in(x740);
		Expression x743=x713.join(x27);
		Expression x745=x28.closure();
		Expression x747=x226.product(Expression.UNIV);
		Expression x746=Expression.IDEN.intersection(x747);
		Expression x744=x745.union(x746);
		Expression x742=x743.join(x744);
		Formula x741=x721.in(x742);
		Formula x738=x739.or(x741);
		Formula x734=x735.and(x738);
		Expression x749=x723.join(x33);
		Formula x748=x719.in(x749);
		Formula x733=x734.and(x748);
		Formula x729=x730.and(x733);
		Expression x754=x715.join(x27);
		Formula x753=x719.in(x754);
		Expression x757=x713.join(x27);
		Expression x759=x28.closure();
		Expression x761=x226.product(Expression.UNIV);
		Expression x760=Expression.IDEN.intersection(x761);
		Expression x758=x759.union(x760);
		Expression x756=x757.join(x758);
		Formula x755=x719.in(x756);
		Formula x752=x753.or(x755);
		Expression x763=x725.join(x33);
		Formula x762=x721.in(x763);
		Formula x751=x752.and(x762);
		Formula x764=x723.in(x31);
		Formula x750=x751.and(x764);
		Formula x728=x729.and(x750);
		Formula x727=x728.not();
		Formula x765=x725.in(x31);
		Formula x726=x727.or(x765);
		Formula x710=x726.forAll(x711);
		Variable x769=Variable.unary("show_n");
		Decls x768=x769.oneOf(x4);
		Variable x771=Variable.unary("show_p");
		Decls x770=x771.oneOf(x67);
		Variable x773=Variable.unary("show_q");
		Decls x772=x773.oneOf(x67);
		Variable x775=Variable.unary("show_l");
		Decls x774=x775.oneOf(x63);
		Variable x777=Variable.unary("show_l'");
		Decls x776=x777.oneOf(x63);
		Variable x779=Variable.unary("show_s");
		Decls x778=x779.oneOf(x16);
		Variable x781=Variable.unary("show_s'");
		Decls x780=x781.oneOf(x16);
		Variable x783=Variable.unary("show_f");
		Decls x782=x783.oneOf(x16);
		Decls x767=x768.and(x770).and(x772).and(x774).and(x776).and(x778).and(x780).and(x782);
		Expression x790=x769.join(x29);
		Expression x789=x769.union(x790);
		Formula x788=x771.in(x789);
		Expression x795=x769.join(x29);
		Expression x794=x769.union(x795);
		Formula x793=x773.in(x794);
		Expression x798=x773.join(x27);
		Formula x797=x777.in(x798);
		Expression x801=x769.join(x27);
		Expression x803=x28.closure();
		Expression x805=x226.product(Expression.UNIV);
		Expression x804=Expression.IDEN.intersection(x805);
		Expression x802=x803.union(x804);
		Expression x800=x801.join(x802);
		Formula x799=x777.in(x800);
		Formula x796=x797.or(x799);
		Formula x792=x793.and(x796);
		Expression x807=x779.join(x33);
		Formula x806=x775.in(x807);
		Formula x791=x792.and(x806);
		Formula x787=x788.and(x791);
		Expression x812=x771.join(x27);
		Formula x811=x775.in(x812);
		Expression x815=x769.join(x27);
		Expression x817=x28.closure();
		Expression x819=x226.product(Expression.UNIV);
		Expression x818=Expression.IDEN.intersection(x819);
		Expression x816=x817.union(x818);
		Expression x814=x815.join(x816);
		Formula x813=x775.in(x814);
		Formula x810=x811.or(x813);
		Expression x821=x781.join(x33);
		Formula x820=x777.in(x821);
		Formula x809=x810.and(x820);
		Expression x823=x783.join(x32);
		Formula x822=x779.in(x823);
		Formula x808=x809.and(x822);
		Formula x786=x787.and(x808);
		Formula x785=x786.not();
		Expression x825=x783.join(x32);
		Formula x824=x781.in(x825);
		Formula x784=x785.or(x824);
		Formula x766=x784.forAll(x767);
		Variable x829=Variable.unary("show_l");
		Decls x828=x829.oneOf(x63);
		Variable x831=Variable.unary("show_l'");
		Decls x830=x831.oneOf(x63);
		Decls x827=x828.and(x830);
		Expression x837=x31.join(x33);
		Formula x836=x829.in(x837);
		Expression x839=x31.join(x33);
		Formula x838=x831.in(x839);
		Formula x835=x836.and(x838);
		Formula x841=x829.eq(x831);
		Formula x840=x841.not();
		Formula x834=x835.and(x840);
		Formula x833=x834.not();
		Expression x844=x4.join(x29);
		Formula x843=x829.in(x844);
		Expression x846=x4.join(x29);
		Formula x845=x831.in(x846);
		Formula x842=x843.and(x845);
		Formula x832=x833.or(x842);
		Formula x826=x832.forAll(x827);
		Variable x850=Variable.unary("show_s");
		Decls x849=x850.oneOf(x16);
		Variable x852=Variable.unary("show_s'");
		Decls x851=x852.oneOf(x16);
		Decls x848=x849.and(x851);
		Formula x856=x850.in(x31);
		Expression x859=x32.closure();
		Expression x858=x850.join(x859);
		Formula x857=x852.in(x858);
		Formula x855=x856.and(x857);
		Formula x854=x855.not();
		Formula x861=x852.in(x31);
		Formula x860=x861.not();
		Formula x853=x854.or(x860);
		Formula x847=x853.forAll(x848);
		Variable x865=Variable.unary("show_l");
		Decls x864=x865.oneOf(x63);
		Variable x867=Variable.unary("show_l'");
		Decls x866=x867.oneOf(x63);
		Variable x869=Variable.unary("show_p");
		Decls x868=x869.oneOf(x16);
		Decls x863=x864.and(x866).and(x868);
		Expression x876=x869.join(x32);
		Expression x875=x876.join(x33);
		Formula x874=x865.in(x875);
		Expression x879=x869.join(x32);
		Expression x878=x879.join(x33);
		Formula x877=x867.in(x878);
		Formula x873=x874.and(x877);
		Formula x881=x865.eq(x867);
		Formula x880=x881.not();
		Formula x872=x873.and(x880);
		Formula x871=x872.not();
		Expression x884=x4.join(x29);
		Formula x883=x865.in(x884);
		Expression x886=x4.join(x29);
		Formula x885=x867.in(x886);
		Formula x882=x883.and(x885);
		Formula x870=x871.or(x882);
		Formula x862=x870.forAll(x863);
		Variable x890=Variable.unary("show_n");
		Decls x889=x890.oneOf(x6);
		Variable x892=Variable.unary("show_p");
		Decls x891=x892.oneOf(x67);
		Variable x894=Variable.unary("show_q");
		Decls x893=x894.oneOf(x67);
		Variable x896=Variable.unary("show_l");
		Decls x895=x896.oneOf(x63);
		Variable x898=Variable.unary("show_l'");
		Decls x897=x898.oneOf(x63);
		Variable x900=Variable.unary("show_s");
		Decls x899=x900.oneOf(x16);
		Variable x902=Variable.unary("show_s'");
		Decls x901=x902.oneOf(x16);
		Decls x888=x889.and(x891).and(x893).and(x895).and(x897).and(x899).and(x901);
		Expression x909=x890.join(x27);
		Expression x911=x28.closure();
		Expression x913=x226.product(Expression.UNIV);
		Expression x912=Expression.IDEN.intersection(x913);
		Expression x910=x911.union(x912);
		Expression x908=x909.join(x910);
		Formula x907=x892.in(x908);
		Expression x918=x28.closure();
		Expression x917=x892.join(x918);
		Formula x916=x894.in(x917);
		Expression x920=x894.join(x29);
		Formula x919=x898.in(x920);
		Formula x915=x916.and(x919);
		Expression x922=x900.join(x33);
		Formula x921=x896.in(x922);
		Formula x914=x915.and(x921);
		Formula x906=x907.and(x914);
		Expression x925=x892.join(x29);
		Formula x924=x896.in(x925);
		Expression x927=x902.join(x33);
		Formula x926=x898.in(x927);
		Formula x923=x924.and(x926);
		Formula x905=x906.and(x923);
		Formula x904=x905.not();
		Expression x930=x32.closure();
		Expression x929=x900.join(x930);
		Formula x928=x902.in(x929);
		Formula x903=x904.or(x928);
		Formula x887=x903.forAll(x888);
		Expression x932=x6.join(x20);
		Formula x931=x932.eq(x4);
		Expression x934=x4.join(x26);
		Formula x933=x934.eq(x7);
		Expression x936=x7.join(x25);
		Formula x935=x936.eq(x8);
		Expression x938=x4.join(x21);
		Formula x937=x938.eq(x5);
		Expression x940=x5.join(x26);
		Formula x939=x940.eq(x9);
		Expression x942=x9.join(x25);
		Formula x941=x942.eq(x10);
		Expression x944=x10.join(x25);
		Formula x943=x944.eq(x11);
		Expression x946=x5.join(x17);
		Formula x945=x946.eq(x3);
		Expression x948=x3.join(x26);
		Formula x947=x948.eq(x12);
		Expression x950=x12.join(x25);
		Formula x949=x950.eq(x13);
		Formula x951=x0.eq(x0);
		Formula x952=x1.eq(x1);
		Formula x953=x2.eq(x2);
		Formula x954=x3.eq(x3);
		Formula x955=x4.eq(x4);
		Formula x956=x5.eq(x5);
		Formula x957=x6.eq(x6);
		Formula x958=x7.eq(x7);
		Formula x959=x8.eq(x8);
		Formula x960=x9.eq(x9);
		Formula x961=x10.eq(x10);
		Formula x962=x11.eq(x11);
		Formula x963=x12.eq(x12);
		Formula x964=x13.eq(x13);
		Formula x965=x14.eq(x14);
		Formula x966=x15.eq(x15);
		Formula x967=x16.eq(x16);
		Formula x968=x17.eq(x17);
		Formula x969=x18.eq(x18);
		Formula x970=x19.eq(x19);
		Formula x971=x20.eq(x20);
		Formula x972=x21.eq(x21);
		Formula x973=x22.eq(x22);
		Formula x974=x23.eq(x23);
		Formula x975=x24.eq(x24);
		Formula x976=x25.eq(x25);
		Formula x977=x26.eq(x26);
		Formula x978=x27.eq(x27);
		Formula x979=x28.eq(x28);
		Formula x980=x29.eq(x29);
		Formula x981=x30.eq(x30);
		Formula x982=x31.eq(x31);
		Formula x983=x32.eq(x32);
		Formula x984=x33.eq(x33);
		Formula x34=Formula.compose(FormulaOperator.AND, x35, x37, x40, x43, x45, x48, x51, x54, x57, x60, x64, x72, x75, x82, x84, x86, x93, x95, x102, x104, x106, x113, x115, x122, x124, x126, x133, x135, x142, x144, x146, x153, x155, x162, x164, x166, x171, x173, x178, x180, x185, x187, x192, x197, x202, x204, x211, x213, x219, x232, x239, x245, x257, x271, x285, x290, x309, x328, x347, x366, x380, x387, x394, x401, x408, x413, x420, x434, x448, x490, x538, x580, x628, x650, x672, x710, x766, x826, x847, x862, x887, x931, x933, x935, x937, x939, x941, x943, x945, x947, x949, x951, x952, x953, x954, x955, x956, x957, x958, x959, x960, x961, x962, x963, x964, x965, x966, x967, x968, x969, x970, x971, x972, x973, x974, x975, x976, x977, x978, x979, x980, x981, x982, x983, x984);

		Solver solver = new Solver();
		solver.options().setSolver(SATFactory.DefaultSAT4J);
		solver.options().setBitwidth(1);
		//solver.options().setFlatten(false);
		solver.options().setIntEncoding(Options.IntEncoding.TWOSCOMPLEMENT);
		solver.options().setSymmetryBreaking(20);
		solver.options().setSkolemDepth(0);
		System.out.println("Solving...");
		System.out.flush();
		Iterator<Solution> it = solver.solveAll(x34, bounds);
		Solution sol = it.next();
		for(int i=0; i<1; i++){
			System.out.println(sol.toString());
			sol=it.next();
		}
	}}
