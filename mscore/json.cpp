//=============================================================================
//  MuseScore
//  Music Composition & Notation
//
//  Copyright (C) 2002-2019 Werner Schweer
//
//  This program is free software; you can redistribute it and/or modify
//  it under the terms of the GNU General Public License version 2
//  as published by the Free Software Foundation and appearing in
//  the file LICENCE.GPL
//=============================================================================

/**
 File handling: loading and saving.
 */

#include "config.h"
#include "globals.h"
#include "musescore.h"
#include "scoreview.h"
#include "exportmidi.h"
#include "libmscore/xml.h"
#include "libmscore/element.h"
#include "libmscore/note.h"
#include "libmscore/chord.h"
#include "libmscore/rest.h"
#include "libmscore/sig.h"
#include "libmscore/clef.h"
#include "libmscore/key.h"
#include "instrdialog.h"
#include "libmscore/score.h"
#include "libmscore/page.h"
#include "libmscore/dynamic.h"
#include "file.h"
#include "libmscore/style.h"
#include "libmscore/tempo.h"
#include "libmscore/select.h"
#include "libmscore/staff.h"
#include "libmscore/part.h"
#include "libmscore/utils.h"
#include "libmscore/barline.h"
#include "libmscore/slur.h"
#include "libmscore/hairpin.h"
#include "libmscore/ottava.h"
#include "libmscore/textline.h"
#include "libmscore/pedal.h"
#include "libmscore/trill.h"
#include "libmscore/volta.h"
#include "libmscore/timesig.h"
#include "libmscore/box.h"
#include "libmscore/excerpt.h"
#include "libmscore/system.h"
#include "libmscore/tuplet.h"
#include "libmscore/keysig.h"
#include "libmscore/measure.h"
#include "libmscore/undo.h"
#include "libmscore/repeatlist.h"
#include "libmscore/beam.h"
#include "libmscore/stafftype.h"
#include "libmscore/revisions.h"
#include "libmscore/lyrics.h"
#include "libmscore/segment.h"
#include "libmscore/tempotext.h"
#include "libmscore/sym.h"
#include "libmscore/image.h"
#include "synthesizer/msynthesizer.h"
#include "svggenerator.h"
#include "libmscore/tiemap.h"
#include "libmscore/tie.h"
#include "libmscore/measurebase.h"

#include "importmidi/importmidi_instrument.h"

#include "libmscore/chordlist.h"
#include "libmscore/mscore.h"
#include "thirdparty/qzip/qzipreader_p.h"
#include "thirdparty/qzip/qzipwriter_p.h"


namespace Ms {

// From svgc.cpp
//void writeErrorToFile(QString errorstring, QString ofilename);
QString checkSafety(Score * score);
QString getInstrumentName(Instrument * in);
void createAllExcerpts(Score * score);


QJsonArray stavesToJson(Score * score)
      {
      QJsonArray s_ar = QJsonArray();
      for ( Staff * staff: score->staves()) {
            QJsonObject sobj = QJsonObject();

            sobj["type"] = staff->isPitchedStaff(Fraction(0,1))?"standard":(
                           staff->isDrumStaff(Fraction(0,1))?"percussion":(
                           staff->isTabStaff(Fraction(0,1))?"tab":"unknown"));

            s_ar.append(sobj);
            }

      return s_ar;
      }

// Check if parts have the same notes
// This is to handle guitar note+tab so it would not set "multiple" as instrument
bool partsAreEqual(Part * p1, Part * p2)
      {

      Score * cs = p1->score();
      if (cs!=p2->score()) {
            qWarning() << "INVALID PARTS COMPARISON";
            return false;
            }

      QList<const Element*> elems;
      for ( Page* page: cs->pages())
            for ( System* sys: page->systems())
                  for (MeasureBase *m: sys->measures())
                        m->scanElements(&elems, collectElements, false);

      QList<int> ticks, pitches;

      // Write down all notes in first part
      for (const Element * e: elems)
            if (e->type() == Ms::ElementType::NOTE) {
                  ChordRest * cr = (ChordRest*)( ((Note*)e)->chord());

                  if (cs->staff(cr->staffIdx())->part()!=p1) continue;

                  ticks.push_back(cr->segment()->tick().ticks());
                  pitches.push_back(((Note*)e)->ppitch());
                  }

      qWarning() << "PARTS COMPARISON SIZE" << ticks.size();

      bool equal = true;

      // Check if they match second part
      for (const Element * e: elems)
            if (e->type() == Ms::ElementType::NOTE) {
                  ChordRest * cr = (ChordRest*)( ((Note*)e)->chord());

                  if (cs->staff(cr->staffIdx())->part()!=p2) continue;

                  equal = equal && ticks.size()>0 &&
                              (ticks.first() == cr->segment()->tick().ticks()) &&
                              (pitches.first() == ((Note*)e)->ppitch());

                  if (!equal) break;

                  ticks.pop_front(); pitches.pop_front();
                  }


      return equal;
      }

QJsonObject getPartsOnsets(Score* score)
      {

      // Collect together all elements belonging to this system!
      QList<const Element*> elems;
      score->scanElements(&elems, collectElements, true);

      QMap<QString,int> plt;

      QMap<QString,QList<int>> ponsets;
      QMap<QString,QList<bool>> pisrest;

      QMap<QString,int> firstNonRest, lastNonRest;

      Measure* lastm = score->lastMeasure();
      int final_tick = (lastm->tick()+lastm->ticks()).ticks();

      for (const Part * p: score->parts()) {
            QString pid = p->id();
            ponsets[pid] = QList<int>();
            pisrest[pid] = QList<bool>();
            plt[pid] = -1;
            firstNonRest[pid] = final_tick;
            lastNonRest[pid] = 0;
            }

      for (const Element * e: elems) {
            if (e->type() == Ms::ElementType::NOTE ||
                e->type() == Ms::ElementType::REST) {

                  ChordRest * cr = (e->type()==Ms::ElementType::NOTE?
                                          (ChordRest*)( ((Note*)e)->chord()):(ChordRest*)e);

                  int tick = cr->segment()->tick().ticks();

                  QString pid = cr->part()->id();

                  // Update the bounds for actual audio
                  if (e->type() == Ms::ElementType::NOTE) {
                        if (tick<firstNonRest[pid])
                              firstNonRest[pid] = tick;
                        int dur = cr->durationTypeTicks().ticks();
                        if (tick+dur > lastNonRest[pid])
                              lastNonRest[pid] = tick+dur;
                        }

                  if (tick > plt[pid]) {
                        ponsets[pid].push_back(tick);
                        pisrest[pid].push_back(e->type() == Ms::ElementType::REST);
                        plt[pid] = tick;
                        }
                  else if (tick == plt[pid]) {
                        pisrest[pid].last() = pisrest[pid].last() && (e->type() == Ms::ElementType::REST);
                        }

                  }
            }

      TempoMap * tempomap = score->tempomap();
      QJsonObject jsonobj = QJsonObject();

      for (QString key: ponsets.keys()) {
            QJsonObject onset_obj = QJsonObject();

            QJsonArray tar, ar, nrar;

            QList<int> consets = ponsets[key];
            QList<bool> cisrest = pisrest[key];

            for (int i=0;i<consets.size();i++) {
                  int tick = consets[i];
                  tar.push_back(tick);
                  ar.push_back(tempomap->tick2time(tick));
                  if (!cisrest[i])
                        nrar.push_back(tick);
                  }

            onset_obj["ticks"] = tar;
            onset_obj["times"] = ar;
            onset_obj["nonrest_ticks"] = nrar;

            onset_obj["beg_tick"] = firstNonRest[key];
            onset_obj["end_tick"] = lastNonRest[key];

            onset_obj["beg_time"] = tempomap->tick2time(firstNonRest[key]);
            onset_obj["end_time"] = tempomap->tick2time(lastNonRest[key]);

            jsonobj[key] = onset_obj;
            }

      return jsonobj;
      }

bool MuseScore::getPartsDescriptions(MasterScore* score, const QString& saveName)
      {

      qreal rel_tempo = score->tempomap()->relTempo();
      score->tempomap()->setRelTempo(1.0);

      //qDebug("LINEARIZE");

      // Linearize the score (for getting all the onsets)
      score = score->unrollRepeats();

      //qDebug("OPEN FILE");

      
      QFile file(saveName);
      file.open(QIODevice::WriteOnly | QIODevice::Text);
      
      QJsonObject obj = QJsonObject();

      // List all parts
      QJsonArray p_ar;
      int pi = 1;
      for ( Part * part: score->masterScore()->parts()) {
            part->setId(QString::number(pi++));

            QJsonObject pobj = QJsonObject();
            pobj["id"] = part->id();
            pobj["instrument"] = getInstrumentName(part->instrument());
            pobj["name"] = part->partName();
            p_ar.append(pobj);
            }
      obj["parts"] = p_ar;


      //qDebug("CREATE ALL EXCERPTS");
      createAllExcerpts(score->masterScore());

      //qDebug("LISTING EXCERPTS");

      // List all excerpts
      QJsonArray e_ar;
      int ei = 0;

      // Create the "Full" excerpt
      qWarning() << "FULL PART";

      QJsonObject eobj = QJsonObject();

      eobj["id"] = QString::number(ei++);
      eobj["title"] = "Full";
      eobj["staves"] = stavesToJson(score);

      QJsonArray ep_ar;

      Part * p0 = NULL; bool equal = true;
      for (Part * part: score->parts()) {
            if (p0==NULL) p0 = part;
            else equal = equal && partsAreEqual(p0,part);

            ep_ar.append(part->id());
            }
      eobj["parts"] = ep_ar;
      eobj["parts_equal"] = equal;

      e_ar.append(eobj);

      // Create the other excerpt objects

      for (Excerpt* e: score->masterScore()->excerpts())  {
            qWarning() << "EXCERPT" << e->title() << e->parts().size();
            eobj = QJsonObject();

            eobj["id"] = QString::number(ei++);
            eobj["title"] = e->title();
            eobj["staves"] = stavesToJson(e->partScore());

            ep_ar = QJsonArray(); p0 = NULL; equal = true;
            for (Part * part: e->parts().toSet()) {
                  qWarning() << " PART" << part->id();
                  if (p0==NULL) p0 = part;
                  else equal = equal && partsAreEqual(p0,part);
                  ep_ar.append(part->id());
                  }
            eobj["parts"] = ep_ar;
            eobj["parts_equal"] = equal;

            e_ar.append(eobj);
            }
      obj["excerpts"] = e_ar;


      //qDebug("GET ONSETS");

      obj["onsets"] = getPartsOnsets(score);

      Measure* lastm = score->lastMeasure();
      obj["total_ticks"] = (lastm->tick()+lastm->ticks()).ticks();
      obj["total_time"] = score->tempomap()->tick2time((lastm->tick()+lastm->ticks()).ticks());

      // Time Signature
      QJsonObject tso = QJsonObject();
      Fraction ts = score->firstMeasure()->timesig();
      tso["numerator"] = ts.numerator();
      tso["denominator"] = ts.denominator();
      // Ticks in fraction form = length of note in whole notes, so timesig.ticks() = length of measure in ticks
      tso["unit_duration"] = (score->tempomap()->tick2time(ts.ticks()) - score->tempomap()->tick2time(0))/ts.denominator();
      obj["timesig"] = tso;


      QString safe = checkSafety(score);
      if (!safe.isEmpty()) obj["score_unsafe"] = safe;

      file.write(QJsonDocument(obj).toJson());
      file.close();

      score->tempomap()->setRelTempo(rel_tempo);

      return true;
      }
}
