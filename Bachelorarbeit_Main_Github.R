# ==============================================================================
# BACHELORARBEIT: Portfoliooptimierung mit Kryptowährungen
# Empirische Analyse unter Verwendung historischer und DCC-GARCH Kovarianzmatrizen
# ==============================================================================

if (!require("rugarch", quietly = TRUE)) install.packages("rugarch")
if (!require("rmgarch", quietly = TRUE)) install.packages("rmgarch")
if (!require("quantmod", quietly = TRUE)) install.packages("quantmod")
if (!require("quadprog", quietly = TRUE)) install.packages("quadprog")
if (!require("Matrix", quietly = TRUE)) install.packages("Matrix")
if (!require("PerformanceAnalytics", quietly = TRUE)) install.packages("PerformanceAnalytics")

library(rugarch)
library(rmgarch)
library(quantmod)
library(quadprog)
library(Matrix)
library(PerformanceAnalytics)

# Pfad für die Plots
plot_pfad <- "Plots_Bachelorarbeit"
if(!dir.exists(plot_pfad)) dir.create(plot_pfad, recursive = TRUE)

Startdatum = "2016-07-01"
Startdatum_Snp = "1960-01-01"
Enddatum = as.POSIXct("2026-07-01")
Fenster_Tage <- 252 # 1 Jahr Rolling Window

# ==============================================================================
# HILFSFUNKTIONEN
# ==============================================================================
add_date <- function(Anlage){
  rn <- rownames(Anlage)
  rn <- substr(rn, 1, 10)
  Anlage$datum <- as.POSIXct(rn)
  Anlage <- Anlage[,c("datum",setdiff(colnames(Anlage),"datum"))]
  return(Anlage)
}
# MVP mit Zielrendite (Markowitz)
# leerverkauf_erlaubt = FALSE -> Long-only: w_i >= 0
# leerverkauf_erlaubt = TRUE  -> Leerverkauf erlaubt,
#                                aber maximal 2x Gross Leverage

berechne_mvp_ziel <- function(kovarianzmatrix,
                              erwartete_renditen,
                              zielrendite,
                              leerverkauf_erlaubt = FALSE,
                              leverage_limit = 2){
  
  n <- ncol(kovarianzmatrix)
  
  # --------------------------------------------------------------------------
  # Kovarianzmatrix symmetrisieren und positiv definit machen
  # --------------------------------------------------------------------------
  
  kovarianzmatrix <- as.matrix(
    nearPD(
      (kovarianzmatrix + t(kovarianzmatrix)) / 2
    )$mat
  )
  
  # --------------------------------------------------------------------------
  # LONG-ONLY
  # --------------------------------------------------------------------------
  
  if(!leerverkauf_erlaubt){
    
    # Feasibility-Check:
    # Die Zielrendite darf nicht höher sein als die höchste erwartete
    # Rendite eines einzelnen Assets.
    max_moegliche_rendite <- max(erwartete_renditen)
    
    if(zielrendite > max_moegliche_rendite){
      return(NULL)
    }
    
    D <- 2 * kovarianzmatrix
    d <- rep(0, n)
    
    # Budget:
    #       sum(w) = 1
    #
    # Zielrendite:
    #       sum(w * mu) >= zielrendite
    #
    # Long-only:
    #       w_i >= 0
    
    Amat <- cbind(
      rep(1, n),
      erwartete_renditen,
      diag(n)
    )
    
    bvec <- c(
      1,
      zielrendite,
      rep(0, n)
    )
    
    loesung <- tryCatch({
      
      solve.QP(
        Dmat = D,
        dvec = d,
        Amat = Amat,
        bvec = bvec,
        meq = 1
      )
      
    }, error = function(e) {
      return(NULL)
    })
    
    if(is.null(loesung)){
      return(NULL)
    }
    
    w <- loesung$solution
    
    # Numerische Rundungsfehler bereinigen
    w[w < 0] <- 0
    
    if(sum(w) <= 0){
      return(NULL)
    }
    
    w <- w / sum(w)
    
    # Post-Prüfung der Zielrendite
    erreichte_rendite <- sum(w * erwartete_renditen)
    
    if(erreichte_rendite + 1e-6 < zielrendite){
      return(NULL)
    }
    
    names(w) <- colnames(kovarianzmatrix)
    
    return(w)
  }
  
  # --------------------------------------------------------------------------
  # SHORT ERLAUBT
  # --------------------------------------------------------------------------
  
  # Sicherheitsprüfung
  if(leverage_limit < 1){
    stop("Das Leverage-Limit muss mindestens 1 betragen.")
  }
  
  D <- 2 * kovarianzmatrix
  d <- rep(0, n)
  
  # --------------------------------------------------------------------------
  # Gross-Leverage:
  #
  #       sum(|w_i|) <= leverage_limit
  #
  # Da solve.QP keine direkten |w_i|-Ausdrücke unterstützt,
  # werden alle möglichen Vorzeichenkombinationen der Gewichte
  # einzeln betrachtet.
  #
  # Bei 2 Assets: 4 Kombinationen
  # Bei 3 Assets: 8 Kombinationen
  # --------------------------------------------------------------------------
  
  vorzeichen_kombinationen <- expand.grid(
    lapply(1:n, function(x) c(-1, 1))
  )
  
  beste_loesung <- NULL
  kleinste_varianz <- Inf
  
  for(j in 1:nrow(vorzeichen_kombinationen)){
    
    vorzeichen <- as.numeric(vorzeichen_kombinationen[j, ])
    
    # ------------------------------------------------------------------------
    # Für diese Vorzeichenkombination gilt:
    #
    # vorzeichen_i * w_i >= 0
    #
    # Dadurch wird sichergestellt, dass das angenommene Vorzeichen
    # tatsächlich zu den Gewichten passt.
    #
    # Außerdem:
    #
    # sum(|w_i|)
    # =
    # sum(vorzeichen_i * w_i)
    #
    # innerhalb dieser Vorzeichenregion.
    # ------------------------------------------------------------------------
    
    sign_constraints <- diag(n)
    
    for(i in 1:n){
      sign_constraints[, i] <- 0
      sign_constraints[i, i] <- vorzeichen[i]
    }
    
    # Gross-Leverage:
    #
    # sum(vorzeichen_i * w_i) <= leverage_limit
    #
    # solve.QP benötigt >=-Restriktionen:
    #
    # -sum(vorzeichen_i * w_i) >= -leverage_limit
    
    leverage_constraint <- -vorzeichen
    
    # ------------------------------------------------------------------------
    # Restriktionen:
    #
    # 1. sum(w) = 1
    # 2. sum(w * mu) >= zielrendite
    # 3. vorzeichen_i * w_i >= 0
    # 4. sum(|w_i|) <= leverage_limit
    # ------------------------------------------------------------------------
    
    Amat <- cbind(
      rep(1, n),
      erwartete_renditen,
      sign_constraints,
      leverage_constraint
    )
    
    bvec <- c(
      1,
      zielrendite,
      rep(0, n),
      -leverage_limit
    )
    
    loesung <- tryCatch({
      
      solve.QP(
        Dmat = D,
        dvec = d,
        Amat = Amat,
        bvec = bvec,
        meq = 1
      )
      
    }, error = function(e) {
      return(NULL)
    })
    
    if(is.null(loesung)){
      next
    }
    
    w <- loesung$solution
    
    # ------------------------------------------------------------------------
    # Sicherheitsprüfungen
    # ------------------------------------------------------------------------
    
    # Budget
    if(abs(sum(w) - 1) > 1e-6){
      next
    }
    
    # Zielrendite
    erreichte_rendite <- sum(w * erwartete_renditen)
    
    if(erreichte_rendite + 1e-6 < zielrendite){
      next
    }
    
    # Tatsächliches Gross Exposure
    gross_leverage <- sum(abs(w))
    
    if(gross_leverage > leverage_limit + 1e-6){
      next
    }
    
    # ------------------------------------------------------------------------
    # Varianz des Portfolios
    # ------------------------------------------------------------------------
    
    portfolio_varianz <- as.numeric(
      t(w) %*% kovarianzmatrix %*% w
    )
    
    # Beste zulässige Lösung speichern
    if(portfolio_varianz < kleinste_varianz){
      
      kleinste_varianz <- portfolio_varianz
      beste_loesung <- w
    }
  }
  
  # Keine zulässige Lösung gefunden
  if(is.null(beste_loesung)){
    return(NULL)
  }
  
  # Numerische Rundungsfehler bei der Budgetrestriktion korrigieren
  beste_loesung <- beste_loesung / sum(beste_loesung)
  
  names(beste_loesung) <- colnames(kovarianzmatrix)
  
  return(beste_loesung)
}

# ==============================================================================
# DATENABRUF & HARMONISIERUNG
# ==============================================================================
cat("Lade Daten...\n")
setSymbolLookup(BTC = list(name = "BTC-USD",src = "yahoo"))
getSymbols("BTC",from = Startdatum, to  = Enddatum)
colnames(BTC) <- gsub("BTC-USD", "BTC", colnames(BTC))

getSymbols("^GSPC",src="yahoo",from = Startdatum_Snp, to = Enddatum)

setSymbolLookup(OIL = list(name = "BZ=F", src = "yahoo"))
getSymbols("OIL", from = Startdatum, to = Enddatum)
colnames(OIL) <- gsub("BZ=F", "OIL", colnames(OIL))

setSymbolLookup(GOLD = list(name = "GC=F",src = "yahoo"))
getSymbols("GOLD",from = Startdatum, to = Enddatum)
colnames(GOLD) <- gsub("GC=F", "GOLD", colnames(GOLD))

BTC <- na.omit(add_date(as.data.frame(BTC)))
SNP <- add_date(as.data.frame(GSPC))
OIL <- na.omit(add_date(as.data.frame(OIL)))
GOLD <- na.omit(add_date(as.data.frame(GOLD)))

gemeinsame_tage <- intersect(intersect(intersect(SNP$datum,GOLD$datum),OIL$datum),BTC$datum)
BTC_g <- BTC[BTC$datum %in% gemeinsame_tage, ]
SNP_g <- SNP[SNP$datum %in% gemeinsame_tage, ]
OIL_g <- OIL[OIL$datum %in% gemeinsame_tage, ]
GOLD_g <- GOLD[GOLD$datum %in% gemeinsame_tage, ]

BTC_returns <- na.omit(c(NA,diff(log(BTC_g$BTC.Close))))
SNP_returns <- na.omit(c(NA, diff(log(SNP_g$GSPC.Close))))
OIL_returns <- na.omit(c(NA, diff(log(OIL_g$OIL.Close))))
GOLD_returns <- na.omit(c(NA, diff(log(GOLD_g$GOLD.Close))))

datum_returns <- BTC_g$datum[-1]
returns <- cbind(SNP=SNP_returns, GOLD=GOLD_returns, BTC=BTC_returns, OIL=OIL_returns)
rownames(returns) <- as.character(datum_returns)

cat("\n--- Datensatz Validierung ---\n")
cat("Erster gemeinsamer Handelstag: ", as.character(min(datum_returns)), "\n")
cat("Letzter gemeinsamer Handelstag:  ", as.character(max(datum_returns)), "\n")
cat("Beobachtungen nach Harmonisierung: ", nrow(returns), "\n\n")

# ==============================================================================
# ZIELRENDITE
# ==============================================================================

Faktor_Outperformance <- 1

snp_vor_backtest <- SNP[SNP$datum < as.POSIXct(Startdatum), ]
snp_returns_vor_backtest <- na.omit(diff(log(snp_vor_backtest$GSPC.Close)))

Zielrendite_tagesbasis <- mean(snp_returns_vor_backtest) * Faktor_Outperformance
#annualisierte Log_rendite
Zielrendite_pa <- Zielrendite_tagesbasis * 252

# Äquivalente einfache Jahresrendite (nur für die Ausgabe)
Zielrendite_einfach_pa <- exp(Zielrendite_pa) - 1

cat("\n--- Zielrendite ---\n")
cat("Historischer Zeitraum: 1960 bis Start des Backtests\n")
cat("Outperformance-Faktor:", Faktor_Outperformance, "\n")
cat("Zielrendite p.a.:", round(Zielrendite_einfach_pa * 100, 2), "%\n")



# ==============================================================================
# DCC-GARCH SPEZIFIKATION
# ==============================================================================
sGarch_spec <- ugarchspec(variance.model = list(model = 'sGARCH',garchOrder = c(1,1)),
                          mean.model = list(armaOrder = c(0,0)), distribution.model = 'std')
sGarch_multi <- multispec(replicate(4, sGarch_spec))
dcc_spec <- dccspec(uspec = sGarch_multi, dccOrder = c(1,1), distribution = "mvt")

# ==============================================================================
# ROLLING BACKTEST (MIT GEWICHTSSPEICHERUNG, TURNOVER & LEERVERKAUF-DIMENSION)
# ==============================================================================

monat_jahr <- format(datum_returns, "%Y-%m")

reb_tage_monatlich <- unname(
  tapply(seq_along(datum_returns), monat_jahr, max)
)

reb_tage_start <- reb_tage_monatlich[
  reb_tage_monatlich >= Fenster_Tage
]

erster_oos_tag <- datum_returns[reb_tage_start[1] + 1]

# ==============================================================================
# PORTFOLIO-UNIVERSEN & LEERVERKAUF-OPTIONEN
# ==============================================================================

univs <- list(
  SNP_GOLD = c("SNP", "GOLD"),
  SNP_BTC = c("SNP", "BTC"),
  SNP_BTC_OIL = c("SNP", "BTC", "OIL")
)

unique_portfolios <- names(univs)

# Leerverkauf-Optionen mit sprechendem Spalten-Suffix
lv_optionen <- c(LongOnly = FALSE, ShortErlaubt = TRUE)

# Alle Ergebnisspalten (Hist/DCC x Portfolio x Leerverkauf-Option) vorab anlegen
spalten_namen <- character(0)
for(p_name in unique_portfolios){
  for(lv_name in names(lv_optionen)){
    spalten_namen <- c(spalten_namen,
                       paste0("Hist_", p_name, "_", lv_name),
                       paste0("DCC_", p_name, "_", lv_name))
  }
}

oos_returns <- data.frame(Datum = datum_returns)
oos_returns$SNP_Only <- NA
for(sp in spalten_namen) oos_returns[[sp]] <- NA

snp_oos_idx <- which(datum_returns >= erster_oos_tag)
oos_returns$SNP_Only[snp_oos_idx] <- returns[snp_oos_idx, "SNP"]

# ==============================================================================
# SPEICHER
# ==============================================================================

gewichte_liste <- list()
feasibility_liste <- list()

cat("Starte Rolling Backtest...\n")

# ==============================================================================
# ROLLING BACKTEST
# ==============================================================================

for(i in 1:(length(reb_tage_start) - 1)) {
  
  t <- reb_tage_start[i]
  t_next <- reb_tage_start[i + 1]
  
  start_t <- t - Fenster_Tage + 1
  
  returns_in <- returns[start_t:t, ]
  oos_daten <- returns[(t + 1):t_next, ]
  
  n_obs <- nrow(returns_in)
  
  mu_t <- colMeans(returns_in)
  cov_hist_full <- cov(returns_in)
  
  dcc_fit <- tryCatch(
    {
      dccfit(
        dcc_spec,
        data = returns_in,
        solver = "solnp",
        fit.control = list(eval.se = FALSE)
      )
    },
    error = function(e) {
      cat(
        "DCC-Fehler bei",
        as.character(datum_returns[t]),
        ":",
        e$message,
        "\n"
      )
      NULL
    }
  )
  
  if(!is.null(dcc_fit) && inherits(dcc_fit, "DCCfit")) {
    
    cov_dcc_full <- rcov(dcc_fit)[,,n_obs]
    
  } else {
    
    cov_dcc_full <- NULL
    
  }
  
  rebal_datum <- as.character(datum_returns[t])
  
  # ============================================================================
  # PORTFOLIOS x LEERVERKAUF-OPTIONEN
  # ============================================================================
  
  for(p_name in unique_portfolios) {
    
    assets <- univs[[p_name]]
    
    sub_cov_hist <- cov_hist_full[assets, assets, drop = FALSE]
    sub_mu <- mu_t[assets]
    
    if(!is.null(cov_dcc_full)) {
      sub_cov_dcc <- cov_dcc_full[assets, assets, drop = FALSE]
    } else {
      sub_cov_dcc <- NULL
    }
    
    for(lv_name in names(lv_optionen)) {
      
      lv_flag <- lv_optionen[[lv_name]]
      
      # --------------------------------------------------------------------
      # Portfoliooptimierung: historisch & DCC
      # --------------------------------------------------------------------
      
      w_hist <- berechne_mvp_ziel(sub_cov_hist, sub_mu, Zielrendite_tagesbasis,
                                  leerverkauf_erlaubt = lv_flag)
      
      if(!is.null(sub_cov_dcc)) {
        w_dcc <- berechne_mvp_ziel(sub_cov_dcc, sub_mu, Zielrendite_tagesbasis,
                                   leerverkauf_erlaubt = lv_flag)
      } else {
        w_dcc <- NULL
      }
      
      # --------------------------------------------------------------------
      # FEASIBILITY SPEICHERN
      # --------------------------------------------------------------------
      
      feasibility_liste[[length(feasibility_liste) + 1]] <- data.frame(
        Datum = rebal_datum,
        Portfolio = p_name,
        Leerverkauf = lv_name,
        Hist_Feasible = !is.null(w_hist),
        DCC_Feasible = !is.null(w_dcc)
      )
      
      # --------------------------------------------------------------------
      # HISTORISCHES KOVARIANZMODELL
      # --------------------------------------------------------------------
      
      if(!is.null(w_hist)) {
        
        # Asset-Log-Renditen des OOS-Zeitraums in einfache Renditen umwandeln
        diskret_daten <- exp(as.matrix(oos_daten[, assets])) - 1
        
        # Gewichte unmittelbar nach dem Rebalancing
        w_aktuell <- w_hist
        
        # Speicher für tägliche Portfolio-Log-Renditen
        portfolio_log_returns <- rep(NA_real_, nrow(diskret_daten))
        
        for(d in seq_len(nrow(diskret_daten))) {
          
          asset_returns_tag <- as.numeric(diskret_daten[d, ])
          
          # Portfoliorendite mit den zu Beginn dieses Tages
          # tatsächlich vorhandenen Gewichten
          portfolio_ret_tag <- sum(w_aktuell * asset_returns_tag)
          
          # Sicherheitsprüfung
          if(!is.finite(portfolio_ret_tag) || (1 + portfolio_ret_tag) <= 0) {
            break
          }
          
          # Einfache Portfoliorendite wieder als Log-Rendite speichern
          portfolio_log_returns[d] <- log1p(portfolio_ret_tag)
          
          # Gewichte aufgrund der Wertentwicklung der Assets fortschreiben
          # Kein Rebalancing innerhalb des Monats
          w_aktuell <- w_aktuell * (1 + asset_returns_tag)
          w_aktuell <- w_aktuell / (1 + portfolio_ret_tag)
        }
        
        oos_returns[
          (t + 1):t_next,
          paste0("Hist_", p_name, "_", lv_name)
        ] <- portfolio_log_returns
        
        for(asset in assets) {
          gewichte_liste[[length(gewichte_liste) + 1]] <- data.frame(
            Datum = rebal_datum,
            Index = t,
            Portfolio = p_name,
            Leerverkauf = lv_name,
            Modell = "Hist",
            Asset = asset,
            Gewicht = w_hist[asset]
          )
        }
      }
      
      
      # --------------------------------------------------------------------
      # DCC-GARCH-KOVARIANZMODELL
      # --------------------------------------------------------------------
      
      if(!is.null(w_dcc)) {
        
        # Asset-Log-Renditen des OOS-Zeitraums in einfache Renditen umwandeln
        diskret_daten <- exp(as.matrix(oos_daten[, assets])) - 1
        
        # Gewichte unmittelbar nach dem Rebalancing
        w_aktuell <- w_dcc
        
        # Speicher für tägliche Portfolio-Log-Renditen
        portfolio_log_returns <- rep(NA_real_, nrow(diskret_daten))
        
        for(d in seq_len(nrow(diskret_daten))) {
          
          asset_returns_tag <- as.numeric(diskret_daten[d, ])
          
          # Portfoliorendite mit den zu Beginn dieses Tages
          # tatsächlich vorhandenen Gewichten
          portfolio_ret_tag <- sum(w_aktuell * asset_returns_tag)
          
          # Sicherheitsprüfung
          if(!is.finite(portfolio_ret_tag) || (1 + portfolio_ret_tag) <= 0) {
            break
          }
          
          # Einfache Portfoliorendite wieder als Log-Rendite speichern
          portfolio_log_returns[d] <- log1p(portfolio_ret_tag)
          
          # Gewichte aufgrund der Wertentwicklung der Assets fortschreiben
          # Kein Rebalancing innerhalb des Monats
          w_aktuell <- w_aktuell * (1 + asset_returns_tag)
          w_aktuell <- w_aktuell / (1 + portfolio_ret_tag)
        }
        
        oos_returns[
          (t + 1):t_next,
          paste0("DCC_", p_name, "_", lv_name)
        ] <- portfolio_log_returns
        
        for(asset in assets) {
          gewichte_liste[[length(gewichte_liste) + 1]] <- data.frame(
            Datum = rebal_datum,
            Index = t,
            Portfolio = p_name,
            Leerverkauf = lv_name,
            Modell = "DCC",
            Asset = asset,
            Gewicht = w_dcc[asset]
          )
        }
      }
      
    } # Ende for(lv_name)
  } # Ende for(p_name)
} # Ende for(i)


for(p_name in unique_portfolios) {
  for(lv_name in names(lv_optionen)) {
    
    col_dcc  <- paste0("DCC_", p_name, "_", lv_name)
    col_hist <- paste0("Hist_", p_name, "_", lv_name)
    
    dcc_valid  <- !is.na(oos_returns[[col_dcc]])
    hist_valid <- !is.na(oos_returns[[col_hist]])
    
    cat(
      "\n", p_name, "-", lv_name,
      "\nHist gültige Tage:", sum(hist_valid),
      "\nDCC gültige Tage:", sum(dcc_valid),
      "\nBeide gültig:", sum(dcc_valid & hist_valid),
      "\nNur Hist:", sum(hist_valid & !dcc_valid),
      "\nNur DCC:", sum(dcc_valid & !hist_valid),
      "\n"
    )
  }
}

# ==============================================================================
# TABELLEN ERSTELLEN
# ==============================================================================

gewichte_tabelle <- do.call(rbind, gewichte_liste)
feasibility_tabelle <- do.call(rbind, feasibility_liste)

# ==============================================================================
# FEASIBILITY-STATISTIK (inkl. Leerverkauf-Dimension)
# ==============================================================================

cat("\n--- Feasibility-Statistik (Wie oft war Zielrendite erreichbar?) ---\n")
print(
  aggregate(
    cbind(Hist_Feasible, DCC_Feasible) ~ Portfolio + Leerverkauf,
    data = feasibility_tabelle,
    FUN = mean
  )
)

# ==============================================================================
# KONTROLLE DER GESPEICHERTEN GEWICHTE
# ==============================================================================

cat("\n--- Kontrolle Gewichte ---\n")
print(head(gewichte_tabelle))

# Plausibilitätscheck: extreme Hebel bei Leerverkauf sichtbar machen
cat("\n--- Extremwerte der Gewichte (Betrag) je Leerverkauf-Option ---\n")
print(
  aggregate(
    Gewicht ~ Leerverkauf,
    data = gewichte_tabelle,
    FUN = function(x) c(min = round(min(x),2), max = round(max(x),2))
  )
)

# ==============================================================================
# TURNOVER MIT GEWICHTSDRIFT 
# ==============================================================================

turnover_ergebnisse <- list()

for(p in unique(gewichte_tabelle$Portfolio)) {
  for(lv_name in unique(gewichte_tabelle$Leerverkauf)) {
    for(m in unique(gewichte_tabelle$Modell)) {
      
      sub_w <- subset(gewichte_tabelle, Portfolio == p & Leerverkauf == lv_name & Modell == m)
      sub_w <- sub_w[order(sub_w$Index, sub_w$Asset), ]
      
      indices <- sort(unique(sub_w$Index))
      t_werte <- c()
      
      if(length(indices) >= 2) {
        for(k in 2:length(indices)) {
          
          idx_prev <- indices[k - 1]
          idx_curr <- indices[k]
          
          # Turnover nur zwischen unmittelbar aufeinanderfolgenden
          # planmäßigen Rebalancing-Zeitpunkten berechnen
          pos_prev <- match(idx_prev, reb_tage_start)
          pos_curr <- match(idx_curr, reb_tage_start)
          
          if(
            is.na(pos_prev) ||
            is.na(pos_curr) ||
            pos_curr != pos_prev + 1
          ) {
            next
          }
          
          prev_data <- subset(sub_w, Index == idx_prev)
          curr_data <- subset(sub_w, Index == idx_curr)
          
          assets <- intersect(prev_data$Asset, curr_data$Asset)
          if(length(assets) == 0) next
          
          w_prev <- prev_data$Gewicht[match(assets, prev_data$Asset)]
          w_curr <- curr_data$Gewicht[match(assets, curr_data$Asset)]
          
          if(any(is.na(w_prev)) || any(is.na(w_curr))) next
          
          if(idx_prev + 1 <= idx_curr) {
            
            ret_period <- returns[(idx_prev + 1):idx_curr, assets, drop = FALSE]
            gross_returns <- exp(colSums(ret_period, na.rm = TRUE))
            
            w_drift <- w_prev * gross_returns
            
            if(sum(w_drift) <= 0 || any(!is.finite(w_drift))) next
            
            w_drift <- w_drift / sum(w_drift)
            
            turnover <- 0.5 * sum(abs(w_curr - w_drift))
            t_werte <- c(t_werte, turnover)
          }
        }
      }
      turnover_ergebnisse[[length(turnover_ergebnisse) + 1]] <- data.frame(
        Portfolio = p,
        Leerverkauf = lv_name,
        Modell = m,
        Mean_Turnover = if(length(t_werte) > 0) mean(t_werte) else NA
      )
    }
  }
}

turnover_tabelle <- do.call(rbind, turnover_ergebnisse)

cat("\n--- Portfolio Turnover (mit Gewichtsdrift) ---\n")
print(turnover_tabelle)

# ==============================================================================
# SEPARATE OOS PERFORMANCE AUSWERTUNG & TABELLE
# ==============================================================================
cat("\n--- Out-of-Sample Performance pro Portfolio ---\n")
berechne_metriken <- function(ret_vec) {
  
  valid <- is.finite(ret_vec)
  clean_r <- ret_vec[valid]
  
  if(length(clean_r) < 10) {
    return(c(NA, NA, NA, NA))
  }
  
  # Log-Renditen -> einfache Renditen
  simple_r <- exp(clean_r) - 1
  
  # Annualisierte geometrische Rendite
  ann_ret <- exp(mean(clean_r) * 252) - 1
  
  # Annualisierte Volatilität
  ann_vol <- sd(simple_r) * sqrt(252)
  
  # Rendite-Volatilitäts-Verhältnis
  rendite_vola_ratio <- ann_ret / ann_vol
  
  # Maximaler Drawdown auf Basis einfacher Renditen
  max_dd <- maxDrawdown(
    xts(
      simple_r,
      order.by = oos_returns$Datum[valid]
    )
  )
  
  return(c(
    Rendite_pa = round(ann_ret * 100, 2),
    Vola_pa = round(ann_vol * 100, 2),
    Rendite_Vola_Ratio = round(rendite_vola_ratio, 3),
    Max_DD = round(max_dd * 100, 2)
  ))
}

perf_matrix <- t(sapply(oos_returns[,-1], berechne_metriken))
colnames(perf_matrix) <- c("Rendite (% p.a.)", "Volatilität (% p.a.)", "Rendite-Vola-Ratio", "Max Drawdown (%)")
print(perf_matrix)

# ==============================================================================
# STATISTISCHER SIGNIFIKANZTEST (Memmel-Korrektur), je Leerverkauf-Option
# ==============================================================================
cat("\n--- Statistischer Performance-Vergleich (DCC vs. Historisch) ---\n")

test_sharpe_memmel <- function(ret1, ret2) {
  valid <- is.finite(ret1) & is.finite(ret2)
  r1 <- ret1[valid]; r2 <- ret2[valid]
  
  # Portfolio-Log-Renditen in einfache Renditen umwandeln
  r1 <- exp(r1) - 1
  r2 <- exp(r2) - 1
  
  T_obs <- length(r1)
  if(T_obs < 10) return(c(Ratio_DCC = NA, Ratio_Hist = NA, P_Wert = NA, T_obs = T_obs))
  mu1 <- mean(r1); mu2 <- mean(r2)
  sig1 <- sd(r1); sig2 <- sd(r2)
  sh1 <- mu1 / sig1; sh2 <- mu2 / sig2
  rho <- cor(r1, r2)
  var_diff <- (1 / T_obs) * ( 2 * (1 - rho) + 0.5 * (sh1^2 + sh2^2 - 2 * rho^2 * sh1 * sh2))
  z_stat <- (sh1 - sh2) / sqrt(var_diff)
  p_val <- 2 * (1 - pnorm(abs(z_stat)))
  return(c(Ratio_DCC = sh1*sqrt(252), Ratio_Hist = sh2*sqrt(252), P_Wert = p_val, T_obs = T_obs))
}

for(p_name in unique_portfolios) {
  for(lv_name in names(lv_optionen)) {
    col_dcc <- paste0("DCC_", p_name, "_", lv_name)
    col_hist <- paste0("Hist_", p_name, "_", lv_name)
    res_test <- test_sharpe_memmel(oos_returns[[col_dcc]], oos_returns[[col_hist]])
    cat(sprintf("Portfolio %s (%s) -> DCC Ratio: %.3f | Hist Ratio: %.3f | p-Wert: %.4f | n=%d\n",
                p_name, lv_name, res_test[1], res_test[2], res_test[3], res_test[4]))
  }
}

# ==============================================================================
# DCC KORRELATIONS-PLOT (S&P 500 & BTC), illustrativ über Gesamtstichprobe
# ==============================================================================
cat("\nErstelle DCC-Korrelationsplot über die gesamte Stichprobe...\n")
dcc_fit_full <- dccfit(dcc_spec, data = returns, solver = "solnp", fit.control = list(eval.se = FALSE))
dcc_corr_array <- rcor(dcc_fit_full)
snp_btc_corr <- dcc_corr_array["SNP", "BTC", ]

png(file.path(plot_pfad, "DCC_Korrelation_SNP_BTC.png"), width = 900, height = 600, res=150)
plot(datum_returns, snp_btc_corr, type = "l", col = "blue", lwd = 1.5,
     xlab = "", ylab = "DCC-Korrelation",
     main = "Dynamische bedingte Korrelation: S&P 500 & Bitcoin")
abline(h = mean(snp_btc_corr), col = "red", lty = 2)
legend("topright", legend = c("DCC Korrelation", "Mittelwert"), col = c("blue", "red"), lty = c(1, 2))
grid()
dev.off()

# ==============================================================================
# BTC-SENSITIVITÄTSANALYSE
# Historische und DCC-GARCH-Kovarianz, 1-Jahres- vs. 3-Jahres-Schätzfenster
#
# Fragestellung:
# Wie verändert sich das optimale Long-Only-Portfolio bei unterschiedlichen
# Annahmen über die erwartete jährliche BTC-Rendite?
#
# Zusätzlich wird bei gleicher Zielrendite die minimale Varianz mit und ohne
# BTC verglichen. Die Analyse wird sowohl mit der historischen Kovarianzmatrix
# als auch mit der DCC-GARCH-Kovarianzmatrix durchgeführt.
# ==============================================================================

# ------------------------------------------------------------------------------
# 1. Funktion für die Sensitivitätsanalyse
# ------------------------------------------------------------------------------

analysiere_btc_sensitivitaet <- function(
    cov_matrix,
    mu_andere,
    zielrendite,
    btc_renditen_pa,
    portfolio_name,
    modell_name
) {
  
  assets <- colnames(cov_matrix)
  
  # --------------------------------------------------------------------------
  # Vergleichsportfolio OHNE BTC
  # --------------------------------------------------------------------------
  
  assets_ohne_btc <- setdiff(assets, "BTC")
  
  cov_ohne_btc <- cov_matrix[
    assets_ohne_btc,
    assets_ohne_btc,
    drop = FALSE
  ]
  
  mu_ohne_btc <- mu_andere[assets_ohne_btc]
  
  w_ohne_btc <- berechne_mvp_ziel(
    kovarianzmatrix = cov_ohne_btc,
    erwartete_renditen = mu_ohne_btc,
    zielrendite = zielrendite,
    leerverkauf_erlaubt = FALSE
  )
  
  baseline_feasible <- !is.null(w_ohne_btc)
  
  if(baseline_feasible) {
    baseline_varianz <- as.numeric(
      t(w_ohne_btc) %*% cov_ohne_btc %*% w_ohne_btc
    )
    
    baseline_vola_pa <- sqrt(baseline_varianz * 252)
  } else {
    baseline_varianz <- NA_real_
    baseline_vola_pa <- NA_real_
  }
  
  # --------------------------------------------------------------------------
  # Sensitivität gegenüber der angenommenen BTC-Rendite
  # --------------------------------------------------------------------------
  
  ergebnisse <- vector("list", length(btc_renditen_pa))
  
  for(j in seq_along(btc_renditen_pa)) {
    
    btc_rendite_pa <- btc_renditen_pa[j]
    
    # Jährliche einfache BTC-Rendite wird intern in eine tägliche
    # erwartete Log-Rendite umgerechnet.
    mu_btc_taeglich <- log1p(btc_rendite_pa) / 252
    
    mu_full <- c(
      mu_andere,
      BTC = mu_btc_taeglich
    )
    
    mu_full <- mu_full[assets]
    
    w <- berechne_mvp_ziel(
      kovarianzmatrix = cov_matrix,
      erwartete_renditen = mu_full,
      zielrendite = zielrendite,
      leerverkauf_erlaubt = FALSE
    )
    
    feasible <- !is.null(w)
    
    if(feasible) {
      
      portfolio_varianz <- as.numeric(
        t(w) %*% cov_matrix %*% w
      )
      
      portfolio_vola_pa <- sqrt(portfolio_varianz * 252)
      
      btc_gewicht <- unname(w["BTC"])
      
      if(baseline_feasible) {
        varianzreduktion_pct <- (
          1 - portfolio_varianz / baseline_varianz
        ) * 100
      } else {
        varianzreduktion_pct <- NA_real_
      }
      
    } else {
      
      portfolio_varianz <- NA_real_
      portfolio_vola_pa <- NA_real_
      btc_gewicht <- NA_real_
      varianzreduktion_pct <- NA_real_
    }
    
    # Numerisches Rauschen sehr nahe bei 0 wird bereits auf Einzelfenster-Ebene
    # als exakt 0 behandelt.
    if(is.finite(btc_gewicht) && abs(btc_gewicht) < 1e-8) {
      btc_gewicht <- 0
    }
    
    if(is.finite(varianzreduktion_pct) &&
       abs(varianzreduktion_pct) < 1e-8) {
      varianzreduktion_pct <- 0
    }
    
    ergebnisse[[j]] <- data.frame(
      Modell = modell_name,
      Portfolio = portfolio_name,
      BTC_Erwartung_pa = btc_rendite_pa,
      BTC_Gewicht = btc_gewicht,
      Portfolio_Varianz = portfolio_varianz,
      Portfolio_Vola_pa = portfolio_vola_pa,
      Feasible = feasible,
      Baseline_Feasible = baseline_feasible,
      Baseline_Varianz = baseline_varianz,
      Baseline_Vola_pa = baseline_vola_pa,
      Varianzreduktion_pct = varianzreduktion_pct
    )
  }
  
  return(do.call(rbind, ergebnisse))
}


# ==============================================================================
# 2. Sensitivitätsanalyse durchführen
# ==============================================================================

sensitivitaet_ergebnisse <- list()

sensitivitaet_portfolios <- list(
  SNP_BTC = c("SNP", "BTC"),
  SNP_BTC_OIL = c("SNP", "BTC", "OIL")
)

# 5-Prozentpunkte-Schritte von -50 % bis +100 % p.a.
btc_renditen_pa <- seq(
  from = -0.50,
  to = 1.00,
  by = 0.05
)

fenster_optionen_sens <- c(
  "1 Jahr" = 252,
  "3 Jahre" = 756
)

cat("\n")
cat("============================================================\n")
cat("BTC-SENSITIVITÄTSANALYSE\n")
cat("============================================================\n")
cat("BTC-Erwartungsrenditen:",
    paste(round(btc_renditen_pa * 100, 0), collapse = "%, "),
    "% p.a.\n")


for(fenster_name in names(fenster_optionen_sens)) {
  
  fenster <- fenster_optionen_sens[[fenster_name]]
  
  for(p_name in names(sensitivitaet_portfolios)) {
    
    assets <- sensitivitaet_portfolios[[p_name]]
    
    ergebnisse_fenster <- list()
    
    # Nur Rebalancing-Zeitpunkte verwenden, für die das
    # entsprechende historische Fenster vollständig vorhanden ist.
    gueltige_t <- reb_tage_start[
      reb_tage_start >= fenster
    ]
    
    cat("\n")
    cat("------------------------------------------------------------\n")
    cat(p_name, "-", fenster_name, "\n")
    cat("Anzahl Rolling-Fenster:", length(gueltige_t), "\n")
    cat("------------------------------------------------------------\n")
    
    for(t in gueltige_t) {
      
      start <- t - fenster + 1
      
      # Für die DCC-GARCH-Schätzung werden wie im Rolling-Backtest
      # alle verfügbaren Assets verwendet. Anschließend werden die für
      # das jeweilige Portfolio benötigten Kovarianzen herausgeschnitten.
      returns_in_full <- returns[
        start:t,
        ,
        drop = FALSE
      ]
      
      returns_in <- returns_in_full[
        ,
        assets,
        drop = FALSE
      ]
      
      # Erwartete Renditen der anderen Assets werden aus dem
      # jeweiligen historischen Fenster geschätzt.
      mu_andere <- colMeans(
        returns_in[, setdiff(assets, "BTC"), drop = FALSE]
      )
      
      # ------------------------------------------------------------------------
      # HISTORISCHE KOVARIANZ
      # ------------------------------------------------------------------------
      
      cov_hist <- cov(returns_in)
      
      ergebnisse_hist <- analysiere_btc_sensitivitaet(
        cov_matrix = cov_hist,
        mu_andere = mu_andere,
        zielrendite = Zielrendite_tagesbasis,
        btc_renditen_pa = btc_renditen_pa,
        portfolio_name = p_name,
        modell_name = "Historisch"
      )
      
      ergebnisse_hist$Datum <- as.character(datum_returns[t])
      ergebnisse_hist$Fenster <- fenster_name
      
      # ------------------------------------------------------------------------
      # DCC-GARCH-KOVARIANZ
      # ------------------------------------------------------------------------
      
      dcc_fit_sens <- tryCatch(
        {
          dccfit(
            dcc_spec,
            data = returns_in_full,
            solver = "solnp",
            fit.control = list(eval.se = FALSE)
          )
        },
        error = function(e) {
          cat(
            "DCC-Sensitivitätsfehler bei",
            as.character(datum_returns[t]),
            "(", p_name, ", ", fenster_name, "):",
            e$message,
            "\n"
          )
          NULL
        }
      )
      
      if(!is.null(dcc_fit_sens) && inherits(dcc_fit_sens, "DCCfit")) {
        
        n_obs_sens <- nrow(returns_in_full)
        cov_dcc_full <- rcov(dcc_fit_sens)[,,n_obs_sens]
        cov_dcc <- cov_dcc_full[assets, assets, drop = FALSE]
        
        ergebnisse_dcc <- analysiere_btc_sensitivitaet(
          cov_matrix = cov_dcc,
          mu_andere = mu_andere,
          zielrendite = Zielrendite_tagesbasis,
          btc_renditen_pa = btc_renditen_pa,
          portfolio_name = p_name,
          modell_name = "DCC-GARCH"
        )
        
        ergebnisse_dcc$Datum <- as.character(datum_returns[t])
        ergebnisse_dcc$Fenster <- fenster_name
        
      } else {
        
        # Falls die DCC-Schätzung für ein Fenster fehlschlägt, werden für
        # dieses Fenster keine DCC-Ergebnisse erzeugt. Die historische
        # Sensitivitätsanalyse bleibt davon unberührt.
        ergebnisse_dcc <- NULL
      }
      
      # ------------------------------------------------------------------------
      # Ergebnisse zusammenführen
      # ------------------------------------------------------------------------
      
      spalten_reihenfolge <- c(
        "Datum",
        "Fenster",
        "Modell",
        "Portfolio",
        "BTC_Erwartung_pa",
        "BTC_Gewicht",
        "Portfolio_Varianz",
        "Portfolio_Vola_pa",
        "Feasible",
        "Baseline_Feasible",
        "Baseline_Varianz",
        "Baseline_Vola_pa",
        "Varianzreduktion_pct"
      )
      
      ergebnisse_hist <- ergebnisse_hist[, spalten_reihenfolge]
      
      if(!is.null(ergebnisse_dcc)) {
        ergebnisse_dcc <- ergebnisse_dcc[, spalten_reihenfolge]
      }
      
      ergebnisse_fenster[[length(ergebnisse_fenster) + 1]] <-
        if(is.null(ergebnisse_dcc)) {
          ergebnisse_hist
        } else {
          rbind(ergebnisse_hist, ergebnisse_dcc)
        }
    }
    
    sensitivitaet_ergebnisse[[length(sensitivitaet_ergebnisse) + 1]] <-
      do.call(rbind, ergebnisse_fenster)
  }
}

sensitivitaet_tabelle <- do.call(
  rbind,
  sensitivitaet_ergebnisse
)

rownames(sensitivitaet_tabelle) <- NULL


# ==============================================================================
# 3. Kontrolle der Sensitivitätsergebnisse
# ===============================================================================

cat("\n--- Sensitivitätsanalyse: Feasibility ---\n")

feasibility_aggregation <- aggregate(
  Feasible ~ Modell + Portfolio + Fenster + BTC_Erwartung_pa,
  data = sensitivitaet_tabelle,
  FUN = mean
)

feasibility_aggregation$Feasible_Anteil_pct <-
  round(feasibility_aggregation$Feasible * 100, 2)

feasibility_aggregation$Feasible <- NULL

print(feasibility_aggregation)

cat("\n--- Beispielhafte Sensitivitätsergebnisse ---\n")

beispiel_sens <- sensitivitaet_tabelle[
  order(
    sensitivitaet_tabelle$Modell,
    sensitivitaet_tabelle$Portfolio,
    sensitivitaet_tabelle$Fenster,
    sensitivitaet_tabelle$Datum,
    sensitivitaet_tabelle$BTC_Erwartung_pa
  ),
]

print(head(beispiel_sens, 20))


# ==============================================================================
# 4. Aggregation über alle Rolling-Fenster
#
# Median sowie 10.- und 90.-Perzentil zeigen die zentrale Tendenz
# und die Streuung der optimalen BTC-Gewichte.
# ===============================================================================

aggregierte_sensitivitaet <- list()

for(modell_name in unique(sensitivitaet_tabelle$Modell)) {
  
  for(fenster_name in names(fenster_optionen_sens)) {
    
    for(p_name in names(sensitivitaet_portfolios)) {
      
      sub <- subset(
        sensitivitaet_tabelle,
        Modell == modell_name &
          Fenster == fenster_name &
          Portfolio == p_name
      )
      
      if(nrow(sub) == 0) next
      
      aggregiert <- do.call(
        rbind,
        lapply(
          sort(unique(sub$BTC_Erwartung_pa)),
          function(mu_btc) {
            
            punkt <- sub[
              sub$BTC_Erwartung_pa == mu_btc,
            ]
            
            gewicht_gueltig <- punkt$BTC_Gewicht[
              punkt$Feasible &
                is.finite(punkt$BTC_Gewicht)
            ]
            
            vola_gueltig <- punkt$Portfolio_Vola_pa[
              punkt$Feasible &
                is.finite(punkt$Portfolio_Vola_pa)
            ]
            
            var_reduktion_gueltig <- punkt$Varianzreduktion_pct[
              punkt$Feasible &
                punkt$Baseline_Feasible &
                is.finite(punkt$Varianzreduktion_pct)
            ]
            
            data.frame(
              Modell = modell_name,
              Fenster = fenster_name,
              Portfolio = p_name,
              BTC_Erwartung_pa = mu_btc,
              Feasible_Anteil = mean(punkt$Feasible),
              BTC_Gewicht_Median = if(length(gewicht_gueltig) > 0)
                median(gewicht_gueltig) else NA_real_,
              BTC_Gewicht_P10 = if(length(gewicht_gueltig) > 0)
                as.numeric(quantile(gewicht_gueltig, 0.10)) else NA_real_,
              BTC_Gewicht_P90 = if(length(gewicht_gueltig) > 0)
                as.numeric(quantile(gewicht_gueltig, 0.90)) else NA_real_,
              Portfolio_Vola_Median = if(length(vola_gueltig) > 0)
                median(vola_gueltig) else NA_real_,
              Varianzreduktion_Median = if(length(var_reduktion_gueltig) > 0)
                median(var_reduktion_gueltig) else NA_real_
            )
          }
        )
      )
      
      # Sehr kleine numerische Abweichungen werden als exakt 0 behandelt.
      numerische_spalten <- c(
        "BTC_Gewicht_Median",
        "BTC_Gewicht_P10",
        "BTC_Gewicht_P90",
        "Varianzreduktion_Median"
      )
      
      for(col in numerische_spalten) {
        aggregiert[[col]][
          is.finite(aggregiert[[col]]) &
            abs(aggregiert[[col]]) < 1e-8
        ] <- 0
      }
      
      aggregierte_sensitivitaet[[length(aggregierte_sensitivitaet) + 1]] <-
        aggregiert
    }
  }
}

aggregierte_sensitivitaet_tabelle <- do.call(
  rbind,
  aggregierte_sensitivitaet
)

rownames(aggregierte_sensitivitaet_tabelle) <- NULL


# ==============================================================================
# 5. Gerundete Ausgabetabellen
#
# Die Berechnungen selbst verwenden weiterhin die ungerundeten Werte.
# Nur für die Ausgabe werden die Ergebnisse übersichtlich gerundet.
# ===============================================================================

aggregierte_sensitivitaet_ausgabe <- aggregierte_sensitivitaet_tabelle

aggregierte_sensitivitaet_ausgabe$BTC_Erwartung_pa <-
  round(aggregierte_sensitivitaet_ausgabe$BTC_Erwartung_pa * 100, 0)

aggregierte_sensitivitaet_ausgabe$Feasible_Anteil <-
  round(aggregierte_sensitivitaet_ausgabe$Feasible_Anteil * 100, 2)

aggregierte_sensitivitaet_ausgabe$BTC_Gewicht_Median <-
  round(aggregierte_sensitivitaet_ausgabe$BTC_Gewicht_Median * 100, 2)

aggregierte_sensitivitaet_ausgabe$BTC_Gewicht_P10 <-
  round(aggregierte_sensitivitaet_ausgabe$BTC_Gewicht_P10 * 100, 2)

aggregierte_sensitivitaet_ausgabe$BTC_Gewicht_P90 <-
  round(aggregierte_sensitivitaet_ausgabe$BTC_Gewicht_P90 * 100, 2)

aggregierte_sensitivitaet_ausgabe$Portfolio_Vola_Median <-
  round(aggregierte_sensitivitaet_ausgabe$Portfolio_Vola_Median * 100, 2)

aggregierte_sensitivitaet_ausgabe$Varianzreduktion_Median <-
  round(aggregierte_sensitivitaet_ausgabe$Varianzreduktion_Median, 2)

cat("\n--- Aggregierte BTC-Sensitivität (gerundet) ---\n")
print(aggregierte_sensitivitaet_ausgabe)


# ==============================================================================
# 6. Plot: Medianes BTC-Gewicht mit 10.-/90.-Perzentil
# ===============================================================================

for(modell_name in unique(sensitivitaet_tabelle$Modell)) {
  
  for(p_name in names(sensitivitaet_portfolios)) {
    
    for(fenster_name in names(fenster_optionen_sens)) {
      
      sub <- subset(
        aggregierte_sensitivitaet_tabelle,
        Modell == modell_name &
          Portfolio == p_name &
          Fenster == fenster_name
      )
      
      if(nrow(sub) == 0) next
      
      png(
        file.path(
          plot_pfad,
          paste0(
            "BTC_Sensitivitaet_Gewicht_",
            modell_name,
            "_",
            p_name,
            "_",
            gsub(" ", "_", fenster_name),
            ".png"
          )
        ),
        width = 900,
        height = 600,
        res = 150
      )
      
      plot(
        sub$BTC_Erwartung_pa * 100,
        sub$BTC_Gewicht_Median * 100,
        type = "l",
        lwd = 2,
        xlab = "Angenommene BTC-Erwartungsrendite (% p.a.)",
        ylab = "Medianes BTC-Gewicht (%)",
        main = paste(
          "BTC-Sensitivität:",
          modell_name,
          "-",
          p_name,
          "-",
          fenster_name
        )
      )
      
      lines(
        sub$BTC_Erwartung_pa * 100,
        sub$BTC_Gewicht_P10 * 100,
        lty = 2
      )
      
      lines(
        sub$BTC_Erwartung_pa * 100,
        sub$BTC_Gewicht_P90 * 100,
        lty = 2
      )
      
      abline(h = 0, lty = 3)
      grid()
      
      legend(
        "topright",
        legend = c(
          "Median",
          "10. Perzentil",
          "90. Perzentil"
        ),
        lty = c(1, 2, 2),
        lwd = c(2, 1, 1)
      )
      
      dev.off()
    }
  }
}


# ==============================================================================
# 7. Plot: Median der Portfolio-Volatilität
# ===============================================================================

for(modell_name in unique(sensitivitaet_tabelle$Modell)) {
  
  for(p_name in names(sensitivitaet_portfolios)) {
    
    for(fenster_name in names(fenster_optionen_sens)) {
      
      sub <- subset(
        aggregierte_sensitivitaet_tabelle,
        Modell == modell_name &
          Portfolio == p_name &
          Fenster == fenster_name
      )
      
      if(nrow(sub) == 0) next
      
      png(
        file.path(
          plot_pfad,
          paste0(
            "BTC_Sensitivitaet_Volatilitaet_",
            modell_name,
            "_",
            p_name,
            "_",
            gsub(" ", "_", fenster_name),
            ".png"
          )
        ),
        width = 900,
        height = 600,
        res = 150
      )
      
      plot(
        sub$BTC_Erwartung_pa * 100,
        sub$Portfolio_Vola_Median * 100,
        type = "l",
        lwd = 2,
        xlab = "Angenommene BTC-Erwartungsrendite (% p.a.)",
        ylab = "Median der Portfolio-Volatilität (% p.a.)",
        main = paste(
          "Portfolio-Volatilität:",
          modell_name,
          "-",
          p_name,
          "-",
          fenster_name
        )
      )
      
      grid()
      dev.off()
    }
  }
}


# ==============================================================================
# 8. Plot: Varianzreduktion durch BTC
#
# Nur dort berechnet, wo das Vergleichsportfolio OHNE BTC die Zielrendite
# ebenfalls erreichen kann. Ist die Zielrendite ohne BTC nicht erreichbar,
# bleibt die Varianzreduktion NA, da kein sinnvoller Gleichvergleich möglich ist.
# ===============================================================================

for(modell_name in unique(sensitivitaet_tabelle$Modell)) {
  
  for(p_name in names(sensitivitaet_portfolios)) {
    
    for(fenster_name in names(fenster_optionen_sens)) {
      
      sub <- subset(
        aggregierte_sensitivitaet_tabelle,
        Modell == modell_name &
          Portfolio == p_name &
          Fenster == fenster_name
      )
      
      if(nrow(sub) == 0) next
      
      png(
        file.path(
          plot_pfad,
          paste0(
            "BTC_Varianzreduktion_",
            modell_name,
            "_",
            p_name,
            "_",
            gsub(" ", "_", fenster_name),
            ".png"
          )
        ),
        width = 900,
        height = 600,
        res = 150
      )
      
      plot(
        sub$BTC_Erwartung_pa * 100,
        sub$Varianzreduktion_Median,
        type = "l",
        lwd = 2,
        xlab = "Angenommene BTC-Erwartungsrendite (% p.a.)",
        ylab = "Medianer Varianzvorteil durch BTC (%)",
        main = paste(
          "Varianzvergleich mit vs. ohne BTC:",
          modell_name,
          "-",
          p_name,
          "-",
          fenster_name
        )
      )
      
      abline(h = 0, lty = 2)
      grid()
      dev.off()
    }
  }
}


# ==============================================================================
# 9. Kompakte Feasibility-Auswertung
# ==============================================================================

cat("\n--- Feasibility-Anteil je BTC-Erwartungsrendite (gerundet) ---\n")
print(feasibility_aggregation)


# ==============================================================================
# 10. Kompakte Varianzvergleich-Auswertung
# ===============================================================================

cat("\n--- Medianer Varianzvorteil von BTC (gerundet) ---\n")

varianz_auswertung <- subset(
  aggregierte_sensitivitaet_ausgabe,
  is.finite(Varianzreduktion_Median)
)

print(
  varianz_auswertung[
    c(
      "Modell",
      "Fenster",
      "Portfolio",
      "BTC_Erwartung_pa",
      "Varianzreduktion_Median"
    )
  ]
)


cat("\nSensitivitätsanalyse vollständig durchgelaufen!\n")



# ==============================================================================
# KAPITEL 4: TABELLEN UND ABBILDUNGEN
# ==============================================================================

if (!requireNamespace("gridExtra", quietly = TRUE)) {
  install.packages("gridExtra")
}

# ==============================================================================
# 1. AUSGABEORDNER
# ==============================================================================

kapitel4_pfad <- file.path(
  plot_pfad,
  "Kapitel_4_Ergebnisse"
)

tabellen_pfad <- file.path(
  kapitel4_pfad,
  "Tabellen"
)

abbildungen_pfad <- file.path(
  kapitel4_pfad,
  "Abbildungen"
)

hilfstabellen_pfad <- file.path(
  kapitel4_pfad,
  "Hilfstabellen"
)

for(pfad in c(
  kapitel4_pfad,
  tabellen_pfad,
  abbildungen_pfad,
  hilfstabellen_pfad
)) {
  if(!dir.exists(pfad)) {
    dir.create(
      pfad,
      recursive = TRUE
    )
  }
}

cat("\n")
cat("============================================================\n")
cat("ERSTELLE AUSGABEN FÜR KAPITEL 4\n")
cat("Speicherort:\n")
cat(kapitel4_pfad, "\n")
cat("============================================================\n")


# ==============================================================================
# 2. BEZEICHNUNGEN
# ==============================================================================

portfolio_label <- c(
  SNP_GOLD = "S&P 500 + Gold",
  SNP_BTC = "S&P 500 + Bitcoin",
  SNP_BTC_OIL = "S&P 500 + Bitcoin + Rohöl"
)

portfolio_kurz <- c(
  SNP_GOLD = "S&P + Gold",
  SNP_BTC = "S&P + BTC",
  SNP_BTC_OIL = "S&P + BTC + Öl"
)

leerverkauf_label <- c(
  LongOnly = "Long-Only",
  ShortErlaubt = "Leerverkauf erlaubt"
)

modell_label <- c(
  Hist = "Historisch",
  DCC = "DCC-GARCH",
  Historisch = "Historisch",
  "DCC-GARCH" = "DCC-GARCH"
)

asset_label <- c(
  SNP = "S&P 500",
  GOLD = "Gold",
  BTC = "Bitcoin",
  OIL = "Rohöl"
)


# ==============================================================================
# 3. HILFSFUNKTIONEN FÜR TABELLEN
# ==============================================================================

speichere_tabelle_png <- function(
    tabelle,
    dateiname,
    titel,
    breite = 2800,
    schrift = 11,
    zielordner = tabellen_pfad
) {
  
  tab_plot <- tabelle
  
  tab_plot[] <- lapply(
    tab_plot,
    function(x) {
      x <- as.character(x)
      x[is.na(x)] <- "-"
      x
    }
  )
  
  tab_grob <- gridExtra::tableGrob(
    tab_plot,
    rows = NULL,
    theme = gridExtra::ttheme_minimal(
      base_size = schrift,
      colhead = list(
        fg_params = list(
          fontface = "bold"
        )
      )
    )
  )
  
  titel_grob <- grid::textGrob(
    titel,
    gp = grid::gpar(
      fontsize = 16,
      fontface = "bold"
    )
  )
  
  gesamt_grob <- gridExtra::arrangeGrob(
    titel_grob,
    tab_grob,
    ncol = 1,
    heights = c(
      0.10,
      0.90
    )
  )
  
  hoehe <- max(
    1000,
    350 + 75 * nrow(tabelle)
  )
  
  png(
    filename = file.path(
      zielordner,
      dateiname
    ),
    width = breite,
    height = hoehe,
    res = 200
  )
  
  grid::grid.newpage()
  grid::grid.draw(
    gesamt_grob
  )
  
  dev.off()
}


speichere_csv <- function(
    tabelle,
    dateiname,
    zielordner = tabellen_pfad
) {
  
  write.csv2(
    tabelle,
    file = file.path(
      zielordner,
      dateiname
    ),
    row.names = FALSE
  )
}


# ==============================================================================
# 4.1 DESKRIPTIVE STATISTIK
# ==============================================================================


# ------------------------------------------------------------------------------
# TABELLE 4.1: DESKRIPTIVE STATISTIK
# ------------------------------------------------------------------------------

deskriptive_tabelle <- do.call(
  rbind,
  lapply(
    colnames(returns),
    function(asset) {
      
      log_r <- returns[, asset]
      
      simple_r <- exp(log_r) - 1
      
      data.frame(
        Asset = asset_label[asset],
        
        Beobachtungen =
          sum(is.finite(log_r)),
        
        Rendite_pa =
          round(
            (
              exp(
                mean(
                  log_r,
                  na.rm = TRUE
                ) * 252
              ) - 1
            ) * 100,
            2
          ),
        
        Volatilitaet_pa =
          round(
            sd(
              simple_r,
              na.rm = TRUE
            ) *
              sqrt(252) *
              100,
            2
          ),
        
        Minimum_Tag =
          round(
            min(
              simple_r,
              na.rm = TRUE
            ) * 100,
            2
          ),
        
        Maximum_Tag =
          round(
            max(
              simple_r,
              na.rm = TRUE
            ) * 100,
            2
          )
      )
    }
  )
)

colnames(
  deskriptive_tabelle
) <- c(
  "Asset",
  "Beobachtungen",
  "Rendite p.a. (%)",
  "Volatilität p.a. (%)",
  "Minimum Tagesrendite (%)",
  "Maximum Tagesrendite (%)"
)

speichere_tabelle_png(
  deskriptive_tabelle,
  "Tab_4_1_Deskriptive_Statistik.png",
  "Tabelle 4.1: Deskriptive Statistik"
)

speichere_csv(
  deskriptive_tabelle,
  "Tab_4_1_Deskriptive_Statistik.csv"
)


# ------------------------------------------------------------------------------
# TABELLE 4.2: KORRELATIONSMATRIX
# ------------------------------------------------------------------------------

korrelation <- cor(
  returns,
  use = "complete.obs"
)

korrelation <- round(
  korrelation,
  3
)

rownames(korrelation) <-
  asset_label[
    rownames(korrelation)
  ]

colnames(korrelation) <-
  asset_label[
    colnames(korrelation)
  ]

korrelations_tabelle <- data.frame(
  Asset = rownames(korrelation),
  korrelation,
  row.names = NULL,
  check.names = FALSE
)

speichere_tabelle_png(
  korrelations_tabelle,
  "Tab_4_2_Korrelationsmatrix.png",
  "Tabelle 4.2: Korrelationsmatrix der täglichen Log-Renditen",
  breite = 2300
)

speichere_csv(
  korrelations_tabelle,
  "Tab_4_2_Korrelationsmatrix.csv"
)


# ------------------------------------------------------------------------------
# ABBILDUNG 4.1: KUMULATIVE WERTENTWICKLUNG
#
# Logarithmische Y-Achse verhindert, dass die starke BTC-Entwicklung
# die übrigen Anlageklassen optisch zusammendrückt.
# ------------------------------------------------------------------------------

kumulierte_entwicklung <- exp(
  apply(
    returns,
    2,
    cumsum
  )
)

kumulierte_entwicklung <- sweep(
  kumulierte_entwicklung,
  2,
  kumulierte_entwicklung[1, ],
  "/"
) * 100

farben_assets <- c(
  SNP = "black",
  GOLD = "goldenrod3",
  BTC = "firebrick3",
  OIL = "steelblue3"
)

png(
  file.path(
    abbildungen_pfad,
    "Abb_4_1_Kumulative_Wertentwicklung_Assets.png"
  ),
  width = 1200,
  height = 750,
  res = 150
)

matplot(
  datum_returns,
  kumulierte_entwicklung,
  type = "l",
  lty = 1,
  lwd = 2,
  log = "y",
  col = farben_assets[
    colnames(returns)
  ],
  xlab = "",
  ylab = "Indexierter Wert (Start = 100, logarithmische Skala)",
  main = "Kumulative Wertentwicklung der Anlageklassen"
)

legend(
  "topleft",
  legend = asset_label[
    colnames(returns)
  ],
  col = farben_assets[
    colnames(returns)
  ],
  lty = 1,
  lwd = 2,
  bty = "n"
)

grid()

dev.off()


# ==============================================================================
# 4.2 ERGEBNISSE DER PORTFOLIOOPTIMIERUNG
# ==============================================================================


# ------------------------------------------------------------------------------
# TABELLE 4.3: FEASIBILITY HAUPTBACKTEST
# ------------------------------------------------------------------------------

feasibility_kap4 <- aggregate(
  cbind(
    Hist_Feasible,
    DCC_Feasible
  ) ~ Portfolio + Leerverkauf,
  data = feasibility_tabelle,
  FUN = mean
)

feasibility_kap4$Hist_Feasible <-
  round(
    feasibility_kap4$Hist_Feasible * 100,
    2
  )

feasibility_kap4$DCC_Feasible <-
  round(
    feasibility_kap4$DCC_Feasible * 100,
    2
  )

feasibility_kap4$Portfolio <-
  portfolio_label[
    feasibility_kap4$Portfolio
  ]

feasibility_kap4$Leerverkauf <-
  leerverkauf_label[
    feasibility_kap4$Leerverkauf
  ]

colnames(
  feasibility_kap4
) <- c(
  "Portfolio",
  "Restriktion",
  "Historisch (%)",
  "DCC-GARCH (%)"
)

speichere_tabelle_png(
  feasibility_kap4,
  "Tab_4_3_Feasibility_Hauptbacktest.png",
  "Tabelle 4.3: Anteil zulässiger Optimierungslösungen"
)

speichere_csv(
  feasibility_kap4,
  "Tab_4_3_Feasibility_Hauptbacktest.csv"
)


# ------------------------------------------------------------------------------
# TABELLE 4.4: MEDIANE PORTFOLIOGEWICHTE
# ------------------------------------------------------------------------------

gewichte_median <- aggregate(
  Gewicht ~
    Portfolio +
    Leerverkauf +
    Modell +
    Asset,
  data = gewichte_tabelle,
  FUN = median
)

gewichte_median$Gewicht <-
  round(
    gewichte_median$Gewicht * 100,
    2
  )

gewichte_median_wide <- reshape(
  gewichte_median,
  idvar = c(
    "Portfolio",
    "Leerverkauf",
    "Modell"
  ),
  timevar = "Asset",
  direction = "wide"
)

gewichte_median_wide$Portfolio <-
  portfolio_label[
    gewichte_median_wide$Portfolio
  ]

gewichte_median_wide$Leerverkauf <-
  leerverkauf_label[
    gewichte_median_wide$Leerverkauf
  ]

gewichte_median_wide$Modell <-
  modell_label[
    gewichte_median_wide$Modell
  ]

names(
  gewichte_median_wide
) <- gsub(
  "Gewicht.",
  "",
  names(gewichte_median_wide),
  fixed = TRUE
)

if(
  "SNP" %in%
  names(gewichte_median_wide)
) {
  names(gewichte_median_wide)[
    names(gewichte_median_wide) ==
      "SNP"
  ] <- "S&P 500 (%)"
}

if(
  "GOLD" %in%
  names(gewichte_median_wide)
) {
  names(gewichte_median_wide)[
    names(gewichte_median_wide) ==
      "GOLD"
  ] <- "Gold (%)"
}

if(
  "BTC" %in%
  names(gewichte_median_wide)
) {
  names(gewichte_median_wide)[
    names(gewichte_median_wide) ==
      "BTC"
  ] <- "Bitcoin (%)"
}

if(
  "OIL" %in%
  names(gewichte_median_wide)
) {
  names(gewichte_median_wide)[
    names(gewichte_median_wide) ==
      "OIL"
  ] <- "Rohöl (%)"
}

names(
  gewichte_median_wide
)[
  names(gewichte_median_wide) ==
    "Leerverkauf"
] <- "Restriktion"

speichere_tabelle_png(
  gewichte_median_wide,
  "Tab_4_4_Mediane_Portfoliogewichte.png",
  "Tabelle 4.4: Mediane Zielgewichte der optimierten Portfolios",
  breite = 3000,
  schrift = 10
)

speichere_csv(
  gewichte_median_wide,
  "Tab_4_4_Mediane_Portfoliogewichte.csv"
)


# ------------------------------------------------------------------------------
# ABBILDUNG 4.2: BTC-GEWICHT IM ROLLING BACKTEST
# S&P 500 + BTC, LONG-ONLY
# ------------------------------------------------------------------------------

btc_hist <- subset(
  gewichte_tabelle,
  Portfolio == "SNP_BTC" &
    Leerverkauf == "LongOnly" &
    Modell == "Hist" &
    Asset == "BTC"
)

btc_dcc <- subset(
  gewichte_tabelle,
  Portfolio == "SNP_BTC" &
    Leerverkauf == "LongOnly" &
    Modell == "DCC" &
    Asset == "BTC"
)

btc_hist_plot <- data.frame(
  Datum =
    as.Date(btc_hist$Datum),
  
  Historisch =
    btc_hist$Gewicht * 100
)

btc_dcc_plot <- data.frame(
  Datum =
    as.Date(btc_dcc$Datum),
  
  DCC_GARCH =
    btc_dcc$Gewicht * 100
)

btc_roll_plot <- merge(
  btc_hist_plot,
  btc_dcc_plot,
  by = "Datum",
  all = TRUE
)

btc_roll_plot <- btc_roll_plot[
  order(
    btc_roll_plot$Datum
  ),
]

max_btc_roll <- max(
  c(
    btc_roll_plot$Historisch,
    btc_roll_plot$DCC_GARCH
  ),
  na.rm = TRUE
)

if(
  !is.finite(max_btc_roll) ||
  max_btc_roll <= 0
) {
  max_btc_roll <- 1
}

png(
  file.path(
    abbildungen_pfad,
    "Abb_4_2_BTC_Gewicht_Rolling_Backtest.png"
  ),
  width = 1200,
  height = 750,
  res = 150
)

plot(
  btc_roll_plot$Datum,
  btc_roll_plot$Historisch,
  type = "l",
  lwd = 2,
  col = "steelblue4",
  ylim = c(
    0,
    max_btc_roll * 1.08
  ),
  xlab = "",
  ylab = "BTC-Zielgewicht (%)",
  main = "BTC-Gewicht im Rolling Backtest"
)

lines(
  btc_roll_plot$Datum,
  btc_roll_plot$DCC_GARCH,
  lwd = 2,
  col = "firebrick3"
)

legend(
  "topright",
  legend = c(
    "Historisch",
    "DCC-GARCH"
  ),
  col = c(
    "steelblue4",
    "firebrick3"
  ),
  lty = 1,
  lwd = 2,
  bty = "n"
)

grid()

dev.off()


# ==============================================================================
# 4.3 OUT-OF-SAMPLE-PERFORMANCE
# ==============================================================================


# ------------------------------------------------------------------------------
# TABELLE 4.5: OUT-OF-SAMPLE-PERFORMANCE
# ------------------------------------------------------------------------------

performance_kap4 <- list()

performance_kap4[[1]] <- data.frame(
  Portfolio = "S&P 500",
  Modell = "Benchmark",
  Restriktion = "-",
  
  Rendite_pa =
    perf_matrix[
      "SNP_Only",
      1
    ],
  
  Vola_pa =
    perf_matrix[
      "SNP_Only",
      2
    ],
  
  Rendite_Vola =
    perf_matrix[
      "SNP_Only",
      3
    ],
  
  MaxDD =
    perf_matrix[
      "SNP_Only",
      4
    ]
)

zaehler <- 2

for(
  p_name in unique_portfolios
) {
  
  for(
    lv_name in names(lv_optionen)
  ) {
    
    for(
      modell in c(
        "Hist",
        "DCC"
      )
    ) {
      
      spaltenname <- paste0(
        modell,
        "_",
        p_name,
        "_",
        lv_name
      )
      
      if(
        spaltenname %in%
        rownames(perf_matrix)
      ) {
        
        performance_kap4[[zaehler]] <-
          data.frame(
            Portfolio =
              portfolio_label[p_name],
            
            Modell =
              modell_label[modell],
            
            Restriktion =
              leerverkauf_label[
                lv_name
              ],
            
            Rendite_pa =
              perf_matrix[
                spaltenname,
                1
              ],
            
            Vola_pa =
              perf_matrix[
                spaltenname,
                2
              ],
            
            Rendite_Vola =
              perf_matrix[
                spaltenname,
                3
              ],
            
            MaxDD =
              perf_matrix[
                spaltenname,
                4
              ]
          )
        
        zaehler <- zaehler + 1
      }
    }
  }
}

performance_kap4 <- do.call(
  rbind,
  performance_kap4
)

performance_kap4_ausgabe <-
  performance_kap4

colnames(
  performance_kap4_ausgabe
) <- c(
  "Portfolio",
  "Modell",
  "Restriktion",
  "Rendite p.a. (%)",
  "Volatilität p.a. (%)",
  "Rendite-Vola-Verhältnis",
  "Maximum Drawdown (%)"
)

speichere_tabelle_png(
  performance_kap4_ausgabe,
  "Tab_4_5_OOS_Performance.png",
  "Tabelle 4.5: Out-of-Sample-Performance",
  breite = 3200,
  schrift = 10
)

speichere_csv(
  performance_kap4_ausgabe,
  "Tab_4_5_OOS_Performance.csv"
)


# ------------------------------------------------------------------------------
# ABBILDUNG 4.3: RENDITE-RISIKO-DIAGRAMM
#
# Zwei Panels:
# - Long-Only
# - Leerverkauf erlaubt
#
# Historisch = Blau
# DCC-GARCH  = Rot
#
# Je Portfolio nur EINE Beschriftung.
# Historisch und DCC desselben Portfolios werden durch eine Linie verbunden.
# Beschriftungen werden automatisch so positioniert,
# dass sie möglichst innerhalb des Plotbereichs bleiben.
# ------------------------------------------------------------------------------

rr <- subset(
  performance_kap4,
  is.finite(Rendite_pa) &
    is.finite(Vola_pa)
)

rr_benchmark <- subset(
  rr,
  Modell == "Benchmark"
)

rr_portfolios <- subset(
  rr,
  Modell != "Benchmark"
)

farben_modelle <- c(
  "Historisch" = "steelblue4",
  "DCC-GARCH" = "firebrick3"
)

x_min <- min(
  rr$Vola_pa,
  na.rm = TRUE
)

x_max <- max(
  rr$Vola_pa,
  na.rm = TRUE
)

y_min <- min(
  rr$Rendite_pa,
  na.rm = TRUE
)

y_max <- max(
  rr$Rendite_pa,
  na.rm = TRUE
)

x_span <- x_max - x_min
y_span <- y_max - y_min

if(x_span == 0) {
  x_span <- 1
}

if(y_span == 0) {
  y_span <- 1
}

x_puffer_links <- 0.08 * x_span
x_puffer_rechts <- 0.18 * x_span

y_puffer_unten <- 0.08 * y_span
y_puffer_oben <- 0.12 * y_span

xlim_plot <- c(
  x_min - x_puffer_links,
  x_max + x_puffer_rechts
)

ylim_plot <- c(
  y_min - y_puffer_unten,
  y_max + y_puffer_oben
)

png(
  file.path(
    abbildungen_pfad,
    "Abb_4_3_Rendite_Risiko_Portfolios.png"
  ),
  width = 1600,
  height = 800,
  res = 150
)

par(
  mfrow = c(1, 2),
  mar = c(
    5,
    5,
    4,
    2
  )
)

for(
  restr in c(
    "Long-Only",
    "Leerverkauf erlaubt"
  )
) {
  
  tmp <- subset(
    rr_portfolios,
    Restriktion == restr
  )
  
  plot(
    NA,
    xlim = xlim_plot,
    ylim = ylim_plot,
    xlab = "Annualisierte Volatilität (%)",
    ylab = "Annualisierte Rendite (%)",
    main = restr
  )
  
  # --------------------------------------------------------------------------
  # Benchmark
  # --------------------------------------------------------------------------
  
  if(
    nrow(rr_benchmark) > 0
  ) {
    
    points(
      rr_benchmark$Vola_pa,
      rr_benchmark$Rendite_pa,
      pch = 18,
      cex = 1.5,
      col = "black"
    )
    
    # Benchmark sicher rechts daneben
    text(
      rr_benchmark$Vola_pa,
      rr_benchmark$Rendite_pa,
      labels = "S&P 500",
      pos = 4,
      offset = 0.6,
      cex = 0.78
    )
  }
  
  # --------------------------------------------------------------------------
  # Portfolios
  # --------------------------------------------------------------------------
  
  for(
    p in unique(tmp$Portfolio)
  ) {
    
    tmp_p <- subset(
      tmp,
      Portfolio == p
    )
    
    # Historisch und DCC desselben Portfolios verbinden
    if(
      nrow(tmp_p) >= 2
    ) {
      
      ord <- order(
        tmp_p$Vola_pa
      )
      
      segments(
        x0 = tmp_p$Vola_pa[ord[1]],
        y0 = tmp_p$Rendite_pa[ord[1]],
        x1 = tmp_p$Vola_pa[ord[length(ord)]],
        y1 = tmp_p$Rendite_pa[ord[length(ord)]],
        col = "grey70",
        lwd = 1
      )
    }
    
    # Punkte zeichnen
    for(
      i in seq_len(
        nrow(tmp_p)
      )
    ) {
      
      points(
        tmp_p$Vola_pa[i],
        tmp_p$Rendite_pa[i],
        pch = 19,
        cex = 1.3,
        col =
          farben_modelle[
            tmp_p$Modell[i]
          ]
      )
    }
    
    # Mittelpunkt der beiden Modellvarianten
    x_mitte <- mean(
      tmp_p$Vola_pa
    )
    
    y_mitte <- mean(
      tmp_p$Rendite_pa
    )
    
    # ------------------------------------------------------------------------
    # Automatische Labelposition
    #
    # Wenn der Punkt eher rechts im Plot liegt:
    # Beschriftung links daneben.
    #
    # Wenn er eher links liegt:
    # Beschriftung rechts daneben.
    # ------------------------------------------------------------------------
    
    x_schwelle <- x_min + 0.72 * x_span
    
    if(
      x_mitte > x_schwelle
    ) {
      
      pos_label <- 2
      
    } else {
      
      pos_label <- 4
    }
    
    # Bei sehr hohen Punkten lieber unterhalb beschriften
    y_schwelle <- y_min + 0.82 * y_span
    
    if(
      y_mitte > y_schwelle
    ) {
      
      pos_label <- 1
    }
    
    text(
      x_mitte,
      y_mitte,
      labels = p,
      pos = pos_label,
      offset = 0.6,
      cex = 0.70
    )
  }
  
  legend(
    "topleft",
    legend = c(
      "Historisch",
      "DCC-GARCH",
      "S&P 500"
    ),
    col = c(
      "steelblue4",
      "firebrick3",
      "black"
    ),
    pch = c(
      19,
      19,
      18
    ),
    bty = "n"
  )
  
  grid()
}

par(
  mfrow = c(1, 1)
)

dev.off()
# ------------------------------------------------------------------------------
# TABELLE 4.6: MEMMEL-TEST
# ------------------------------------------------------------------------------

memmel_kap4 <- list()

zaehler <- 1

for(
  p_name in unique_portfolios
) {
  
  for(
    lv_name in names(lv_optionen)
  ) {
    
    col_dcc <- paste0(
      "DCC_",
      p_name,
      "_",
      lv_name
    )
    
    col_hist <- paste0(
      "Hist_",
      p_name,
      "_",
      lv_name
    )
    
    res_test <- test_sharpe_memmel(
      oos_returns[[col_dcc]],
      oos_returns[[col_hist]]
    )
    
    memmel_kap4[[zaehler]] <-
      data.frame(
        Portfolio =
          portfolio_label[
            p_name
          ],
        
        Restriktion =
          leerverkauf_label[
            lv_name
          ],
        
        Sharpe_Historisch =
          round(
            res_test[
              "Ratio_Hist"
            ],
            3
          ),
        
        Sharpe_DCC =
          round(
            res_test[
              "Ratio_DCC"
            ],
            3
          ),
        
        P_Wert =
          round(
            res_test[
              "P_Wert"
            ],
            4
          ),
        
        Beobachtungen =
          as.integer(
            res_test[
              "T_obs"
            ]
          ),
        
        Signifikant_5pct =
          ifelse(
            is.finite(
              res_test[
                "P_Wert"
              ]
            ) &&
              res_test[
                "P_Wert"
              ] < 0.05,
            "Ja",
            "Nein"
          )
      )
    
    zaehler <- zaehler + 1
  }
}

memmel_kap4 <- do.call(
  rbind,
  memmel_kap4
)

colnames(
  memmel_kap4
) <- c(
  "Portfolio",
  "Restriktion",
  "Sharpe Historisch",
  "Sharpe DCC-GARCH",
  "p-Wert",
  "Beobachtungen",
  "Signifikant (5 %)"
)

speichere_tabelle_png(
  memmel_kap4,
  "Tab_4_6_Memmel_Test.png",
  "Tabelle 4.6: Statistischer Vergleich der Sharpe Ratios",
  breite = 3000
)

speichere_csv(
  memmel_kap4,
  "Tab_4_6_Memmel_Test.csv"
)


# ------------------------------------------------------------------------------
# TABELLE 4.7: TURNOVER
# ------------------------------------------------------------------------------

turnover_kap4 <-
  turnover_tabelle

turnover_kap4$Mean_Turnover <-
  round(
    turnover_kap4$Mean_Turnover *
      100,
    2
  )

turnover_kap4 <- reshape(
  turnover_kap4,
  idvar = c(
    "Portfolio",
    "Leerverkauf"
  ),
  timevar = "Modell",
  direction = "wide"
)

turnover_kap4$Portfolio <-
  portfolio_label[
    turnover_kap4$Portfolio
  ]

turnover_kap4$Leerverkauf <-
  leerverkauf_label[
    turnover_kap4$Leerverkauf
  ]

names(
  turnover_kap4
) <- gsub(
  "Mean_Turnover.",
  "",
  names(turnover_kap4),
  fixed = TRUE
)

names(
  turnover_kap4
)[
  names(turnover_kap4) ==
    "Leerverkauf"
] <- "Restriktion"

if(
  "Hist" %in%
  names(turnover_kap4)
) {
  names(
    turnover_kap4
  )[
    names(turnover_kap4) ==
      "Hist"
  ] <- "Historisch (%)"
}

if(
  "DCC" %in%
  names(turnover_kap4)
) {
  names(
    turnover_kap4
  )[
    names(turnover_kap4) ==
      "DCC"
  ] <- "DCC-GARCH (%)"
}

speichere_tabelle_png(
  turnover_kap4,
  "Tab_4_7_Turnover.png",
  "Tabelle 4.7: Durchschnittlicher Portfolio Turnover"
)

speichere_csv(
  turnover_kap4,
  "Tab_4_7_Turnover.csv"
)


# ==============================================================================
# 4.4 BTC-SENSITIVITÄTSANALYSE
# ==============================================================================


# ------------------------------------------------------------------------------
# HILFSFUNKTION:
# MEDIAN + P10 + P90
#
# Median = Schwarz
# P10    = Blau
# P90    = Rot
#
# Y-Achse wird aus allen drei Reihen bestimmt.
# Dadurch können P10/P90 nicht  abgeschnitten werden.
# ------------------------------------------------------------------------------

plot_btc_gewicht_panels <- function(
    portfolio_name,
    titel,
    dateiname
) {
  
  sub_all <- subset(
    aggregierte_sensitivitaet_tabelle,
    Portfolio == portfolio_name
  )
  
  alle_gewichte <- c(
    sub_all$BTC_Gewicht_Median,
    sub_all$BTC_Gewicht_P10,
    sub_all$BTC_Gewicht_P90
  ) * 100
  
  alle_gewichte <-
    alle_gewichte[
      is.finite(
        alle_gewichte
      )
    ]
  
  max_y <- max(
    alle_gewichte,
    na.rm = TRUE
  )
  
  if(
    !is.finite(max_y) ||
    max_y <= 0
  ) {
    max_y <- 1
  }
  
  max_y <- max_y * 1.08
  
  png(
    file.path(
      abbildungen_pfad,
      dateiname
    ),
    width = 1500,
    height = 1100,
    res = 150
  )
  
  par(
    mfrow = c(2, 2),
    mar = c(
      5,
      5,
      4,
      2
    ),
    oma = c(
      1,
      1,
      4,
      1
    )
  )
  
  kombinationen <- list(
    c(
      "Historisch",
      "1 Jahr"
    ),
    c(
      "Historisch",
      "3 Jahre"
    ),
    c(
      "DCC-GARCH",
      "1 Jahr"
    ),
    c(
      "DCC-GARCH",
      "3 Jahre"
    )
  )
  
  for(
    kombi in kombinationen
  ) {
    
    modell <- kombi[1]
    fenster <- kombi[2]
    
    sub <- subset(
      sub_all,
      Modell == modell &
        Fenster == fenster
    )
    
    sub <- sub[
      order(
        sub$BTC_Erwartung_pa
      ),
    ]
    
    if(
      nrow(sub) == 0
    ) {
      
      plot.new()
      
      title(
        main = paste(
          modell,
          "-",
          fenster
        )
      )
      
      next
    }
    
    plot(
      sub$BTC_Erwartung_pa *
        100,
      
      sub$BTC_Gewicht_Median *
        100,
      
      type = "l",
      lwd = 2.5,
      col = "black",
      
      ylim = c(
        0,
        max_y
      ),
      
      xlim = c(
        -50,
        100
      ),
      
      xlab =
        "BTC-Erwartungsrendite (% p.a.)",
      
      ylab =
        "BTC-Gewicht (%)",
      
      main = paste(
        modell,
        "-",
        fenster
      )
    )
    
    lines(
      sub$BTC_Erwartung_pa *
        100,
      
      sub$BTC_Gewicht_P10 *
        100,
      
      lwd = 2,
      lty = 2,
      col = "steelblue4"
    )
    
    lines(
      sub$BTC_Erwartung_pa *
        100,
      
      sub$BTC_Gewicht_P90 *
        100,
      
      lwd = 2,
      lty = 2,
      col = "firebrick3"
    )
    
    abline(
      h = 0,
      lty = 3,
      col = "grey50"
    )
    
    grid()
    
    legend(
      "topright",
      
      legend = c(
        "Median",
        "10. Perzentil",
        "90. Perzentil"
      ),
      
      col = c(
        "black",
        "steelblue4",
        "firebrick3"
      ),
      
      lty = c(
        1,
        2,
        2
      ),
      
      lwd = c(
        2.5,
        2,
        2
      ),
      
      bty = "n",
      cex = 0.85
    )
  }
  
  mtext(
    titel,
    outer = TRUE,
    side = 3,
    line = 1,
    cex = 1.4,
    font = 2
  )
  
  par(
    mfrow = c(1, 1)
  )
  
  dev.off()
}


# ------------------------------------------------------------------------------
# ABBILDUNG 4.4: BTC-GEWICHT S&P + BTC
# ------------------------------------------------------------------------------

plot_btc_gewicht_panels(
  portfolio_name = "SNP_BTC",
  titel = "BTC-Sensitivität: S&P 500 + Bitcoin",
  dateiname =
    "Abb_4_4_BTC_Gewicht_SNP_BTC.png"
)


# ------------------------------------------------------------------------------
# ABBILDUNG 4.5: BTC-GEWICHT S&P + BTC + ROHÖL
# ------------------------------------------------------------------------------

plot_btc_gewicht_panels(
  portfolio_name =
    "SNP_BTC_OIL",
  
  titel =
    "BTC-Sensitivität: S&P 500 + Bitcoin + Rohöl",
  
  dateiname =
    "Abb_4_5_BTC_Gewicht_SNP_BTC_OIL.png"
)


# ------------------------------------------------------------------------------
# ALLGEMEINE HILFSFUNKTION FÜR FEASIBILITY UND VARIANZREDUKTION
#
# Farbe:
# Historisch = Blau
# DCC        = Rot
#
# Linientyp:
# 1 Jahr     = durchgezogen
# 3 Jahre    = gestrichelt
# ------------------------------------------------------------------------------

plot_sensitivitaet_vergleich <- function(
    portfolio_name,
    y_variable,
    y_faktor,
    y_label,
    titel,
    dateiname,
    feste_y_achse = NULL,
    null_linie = FALSE,
    start_bei_null = FALSE,
    legend_position = "topleft"
) {
  
  sub <- subset(
    aggregierte_sensitivitaet_tabelle,
    Portfolio == portfolio_name
  )
  
  sub <- sub[
    order(
      sub$Modell,
      sub$Fenster,
      sub$BTC_Erwartung_pa
    ),
  ]
  
  alle_y <-
    sub[[y_variable]] *
    y_faktor
  
  alle_y <-
    alle_y[
      is.finite(
        alle_y
      )
    ]
  
  if(
    length(alle_y) == 0
  ) {
    return(
      invisible(NULL)
    )
  }
  
  if(
    !is.null(
      feste_y_achse
    )
  ) {
    
    ylim_plot <-
      feste_y_achse
    
  } else {
    
    y_min <- min(
      c(
        alle_y,
        if(null_linie) 0
      ),
      na.rm = TRUE
    )
    
    y_max <- max(
      c(
        alle_y,
        if(null_linie) 0
      ),
      na.rm = TRUE
    )
    
    if(
      start_bei_null &&
      y_min >= 0
    ) {
      y_min <- 0
    }
    
    spannweite <-
      y_max - y_min
    
    if(
      spannweite <= 0
    ) {
      spannweite <- max(
        abs(y_max) * 0.1,
        1
      )
    }
    
    if(
      start_bei_null &&
      y_min == 0
    ) {
      
      ylim_plot <- c(
        0,
        y_max +
          0.08 *
          spannweite
      )
      
    } else {
      
      ylim_plot <- c(
        y_min -
          0.05 *
          spannweite,
        
        y_max +
          0.08 *
          spannweite
      )
    }
  }
  
  png(
    file.path(
      abbildungen_pfad,
      dateiname
    ),
    width = 1200,
    height = 750,
    res = 150
  )
  
  plot(
    NA,
    xlim = c(
      -50,
      100
    ),
    ylim = ylim_plot,
    xlab =
      "Angenommene BTC-Erwartungsrendite (% p.a.)",
    ylab = y_label,
    main = titel,
    yaxt = "n"
  )
  
  y_ticks <- pretty(ylim_plot)
  
  axis(
    side = 2,
    at = y_ticks,
    labels = format(
      y_ticks,
      scientific = FALSE,
      trim = TRUE
    )
  )
  
  # Historisch - 1 Jahr
  tmp <- subset(
    sub,
    Modell == "Historisch" &
      Fenster == "1 Jahr"
  )
  
  lines(
    tmp$BTC_Erwartung_pa *
      100,
    tmp[[y_variable]] *
      y_faktor,
    col = "steelblue4",
    lty = 1,
    lwd = 2
  )
  
  # Historisch - 3 Jahre
  tmp <- subset(
    sub,
    Modell == "Historisch" &
      Fenster == "3 Jahre"
  )
  
  lines(
    tmp$BTC_Erwartung_pa *
      100,
    tmp[[y_variable]] *
      y_faktor,
    col = "steelblue4",
    lty = 2,
    lwd = 2
  )
  
  # DCC-GARCH - 1 Jahr
  tmp <- subset(
    sub,
    Modell == "DCC-GARCH" &
      Fenster == "1 Jahr"
  )
  
  lines(
    tmp$BTC_Erwartung_pa *
      100,
    tmp[[y_variable]] *
      y_faktor,
    col = "firebrick3",
    lty = 1,
    lwd = 2
  )
  
  # DCC-GARCH - 3 Jahre
  tmp <- subset(
    sub,
    Modell == "DCC-GARCH" &
      Fenster == "3 Jahre"
  )
  
  lines(
    tmp$BTC_Erwartung_pa *
      100,
    tmp[[y_variable]] *
      y_faktor,
    col = "firebrick3",
    lty = 2,
    lwd = 2
  )
  
  if(
    null_linie
  ) {
    abline(
      h = 0,
      col = "grey40",
      lty = 3
    )
  }
  legend(
    legend_position,
    
    legend = c(
      "Historisch – 1 Jahr",
      "Historisch – 3 Jahre",
      "DCC-GARCH – 1 Jahr",
      "DCC-GARCH – 3 Jahre"
    ),
    
    col = c(
      "steelblue4",
      "steelblue4",
      "firebrick3",
      "firebrick3"
    ),
    
    lty = c(
      1,
      2,
      1,
      2
    ),
    
    lwd = 2,
    bty = "n"
  )
  
  grid()
  
  dev.off()
}

# ------------------------------------------------------------------------------
# ABBILDUNG 4.6: FEASIBILITY S&P + BTC
# ------------------------------------------------------------------------------

plot_sensitivitaet_vergleich(
  portfolio_name = "SNP_BTC",
  y_variable = "Feasible_Anteil",
  y_faktor = 100,
  y_label =
    "Anteil zulässiger Lösungen (%)",
  titel =
    "Erreichbarkeit der Zielrendite: S&P 500 + Bitcoin",
  dateiname =
    "Abb_4_6_Feasibility_SNP_BTC.png",
  feste_y_achse = c(
    0,
    100
  ),
  legend_position = "bottomright"
)

# ------------------------------------------------------------------------------
# ABBILDUNG 4.7: FEASIBILITY S&P + BTC + ROHÖL
# ------------------------------------------------------------------------------

plot_sensitivitaet_vergleich(
  portfolio_name =
    "SNP_BTC_OIL",
  y_variable =
    "Feasible_Anteil",
  y_faktor = 100,
  y_label =
    "Anteil zulässiger Lösungen (%)",
  titel =
    "Erreichbarkeit der Zielrendite: S&P 500 + Bitcoin + Rohöl",
  dateiname =
    "Abb_4_7_Feasibility_SNP_BTC_OIL.png",
  feste_y_achse = c(
    0,
    100
  ),
  legend_position = "bottomright"
)

# ------------------------------------------------------------------------------
# ABBILDUNG 4.8: VARIANZVORTEIL S&P + BTC
# ------------------------------------------------------------------------------

plot_sensitivitaet_vergleich(
  portfolio_name = "SNP_BTC",
  y_variable =
    "Varianzreduktion_Median",
  y_faktor = 1,
  y_label =
    "Medianer Varianzvorteil durch BTC (%)",
  titel =
    "Varianzvorteil durch Bitcoin: S&P 500 + Bitcoin",
  dateiname =
    "Abb_4_8_Varianzreduktion_SNP_BTC.png",
  null_linie = TRUE,
  start_bei_null = TRUE
)


# ------------------------------------------------------------------------------
# ABBILDUNG 4.9: VARIANZVORTEIL S&P + BTC + ROHÖL
# ------------------------------------------------------------------------------

plot_sensitivitaet_vergleich(
  portfolio_name =
    "SNP_BTC_OIL",
  y_variable =
    "Varianzreduktion_Median",
  y_faktor = 1,
  y_label =
    "Medianer Varianzvorteil durch BTC (%)",
  titel =
    "Varianzvorteil durch Bitcoin: S&P 500 + Bitcoin + Rohöl",
  dateiname =
    "Abb_4_9_Varianzreduktion_SNP_BTC_OIL.png",
  null_linie = TRUE,
  start_bei_null = TRUE
)


# ==============================================================================
# 5. HILFSTABELLEN BTC-SENSITIVITÄT
# ==============================================================================


# ------------------------------------------------------------------------------
# VOLLSTÄNDIGE AGGREGIERTE SENSITIVITÄT ALS CSV
# ------------------------------------------------------------------------------

write.csv2(
  aggregierte_sensitivitaet_ausgabe,
  file = file.path(
    hilfstabellen_pfad,
    "BTC_Sensitivitaet_Vollstaendig.csv"
  ),
  row.names = FALSE
)


# ------------------------------------------------------------------------------
# AUSGEWÄHLTE BTC-RENDITEN FÜR SCHNELLES ABLESEN
# ------------------------------------------------------------------------------

auswahl_btc_renditen <- c(
  -50,
  0,
  25,
  50,
  75,
  100
)

for(
  p_name in c(
    "SNP_BTC",
    "SNP_BTC_OIL"
  )
) {
  
  hilfstabelle <- subset(
    aggregierte_sensitivitaet_ausgabe,
    Portfolio == p_name &
      BTC_Erwartung_pa %in%
      auswahl_btc_renditen
  )
  
  hilfstabelle <- hilfstabelle[
    ,
    c(
      "Modell",
      "Fenster",
      "BTC_Erwartung_pa",
      "Feasible_Anteil",
      "BTC_Gewicht_Median",
      "BTC_Gewicht_P10",
      "BTC_Gewicht_P90",
      "Portfolio_Vola_Median",
      "Varianzreduktion_Median"
    )
  ]
  
  colnames(
    hilfstabelle
  ) <- c(
    "Modell",
    "Fenster",
    "BTC-Rendite p.a. (%)",
    "Feasible (%)",
    "Median BTC-Gewicht (%)",
    "P10 BTC-Gewicht (%)",
    "P90 BTC-Gewicht (%)",
    "Median Portfolio-Vola (%)",
    "Median Varianzvorteil (%)"
  )
  
  if(
    p_name == "SNP_BTC"
  ) {
    
    png_name <-
      "Hilfstabelle_BTC_Sensitivitaet_SNP_BTC.png"
    
    csv_name <-
      "Hilfstabelle_BTC_Sensitivitaet_SNP_BTC.csv"
    
    titel <-
      "BTC-Sensitivität: S&P 500 + Bitcoin"
    
  } else {
    
    png_name <-
      "Hilfstabelle_BTC_Sensitivitaet_SNP_BTC_OIL.png"
    
    csv_name <-
      "Hilfstabelle_BTC_Sensitivitaet_SNP_BTC_OIL.csv"
    
    titel <-
      "BTC-Sensitivität: S&P 500 + Bitcoin + Rohöl"
  }
  
  speichere_tabelle_png(
    hilfstabelle,
    png_name,
    titel,
    breite = 3400,
    schrift = 9,
    zielordner =
      hilfstabellen_pfad
  )
  
  speichere_csv(
    hilfstabelle,
    csv_name,
    zielordner =
      hilfstabellen_pfad
  )
}


# ==============================================================================
# 6. ZUSÄTZLICHE KONTROLLTABELLE FÜR 3-JAHRES-BTC-ERGEBNISSE
# ==============================================================================

btc_3jahre_kontrolle <- subset(
  aggregierte_sensitivitaet_ausgabe,
  Fenster == "3 Jahre"
)[
  ,
  c(
    "Modell",
    "Portfolio",
    "BTC_Erwartung_pa",
    "Feasible_Anteil",
    "BTC_Gewicht_Median",
    "BTC_Gewicht_P10",
    "BTC_Gewicht_P90",
    "Varianzreduktion_Median"
  )
]

colnames(
  btc_3jahre_kontrolle
) <- c(
  "Modell",
  "Portfolio",
  "BTC-Rendite p.a. (%)",
  "Feasible (%)",
  "Median BTC-Gewicht (%)",
  "P10 BTC-Gewicht (%)",
  "P90 BTC-Gewicht (%)",
  "Median Varianzvorteil (%)"
)

speichere_csv(
  btc_3jahre_kontrolle,
  "Kontrolle_BTC_3_Jahre.csv",
  zielordner =
    hilfstabellen_pfad
)


# ==============================================================================
# 7. ABSCHLUSSMELDUNG
# ==============================================================================

cat("\n")
cat("============================================================\n")
cat("KAPITEL-4-AUSGABEN ERFOLGREICH ERSTELLT\n")
cat("\n")
cat("Tabellen:\n")
cat(tabellen_pfad, "\n")
cat("\n")
cat("Abbildungen:\n")
cat(abbildungen_pfad, "\n")
cat("\n")
cat("Hilfstabellen:\n")
cat(hilfstabellen_pfad, "\n")
cat("============================================================\n")


# ==============================================================================
# KONTROLLE: S&P 500 vs. Zielrendite im 1-Jahres-Fenster
# ==============================================================================

fenster <- 252

gueltige_t_1j <- reb_tage_start[
  reb_tage_start >= fenster
]

kontrolle_1j <- do.call(
  rbind,
  lapply(gueltige_t_1j, function(t) {
    
    start <- t - fenster + 1
    
    mu_snp_tag <- mean(
      returns[start:t, "SNP"],
      na.rm = TRUE
    )
    
    data.frame(
      Datum = as.character(datum_returns[t]),
      
      SNP_Rendite_pa =
        (exp(mu_snp_tag * 252) - 1) * 100,
      
      Zielrendite_pa =
        (exp(Zielrendite_tagesbasis * 252) - 1) * 100,
      
      SNP_ueber_Ziel =
        mu_snp_tag >= Zielrendite_tagesbasis
    )
  })
)

cat("\n--- 1-Jahres-Fenster: S&P 500 vs. Zielrendite ---\n")

print(
  summary(kontrolle_1j$SNP_Rendite_pa)
)

cat(
  "\nZielrendite p.a.:",
  round(
    unique(kontrolle_1j$Zielrendite_pa),
    2
  ),
  "%\n"
)

cat(
  "Anteil der 1-Jahres-Fenster, in denen S&P allein die Zielrendite erreicht:",
  round(
    mean(kontrolle_1j$SNP_ueber_Ziel) * 100,
    2
  ),
  "%\n"
)

# ==============================================================================
# KONTROLLE: S&P 500 vs. Zielrendite im 3-Jahres-Fenster
# ==============================================================================

fenster_3j <- 756

gueltige_t_3j <- reb_tage_start[
  reb_tage_start >= fenster_3j
]

kontrolle_3j <- do.call(
  rbind,
  lapply(gueltige_t_3j, function(t) {
    
    start <- t - fenster_3j + 1
    
    mu_snp_tag <- mean(
      returns[start:t, "SNP"],
      na.rm = TRUE
    )
    
    data.frame(
      Datum = as.character(datum_returns[t]),
      
      SNP_Rendite_pa =
        (exp(mu_snp_tag * 252) - 1) * 100,
      
      Zielrendite_pa =
        (exp(Zielrendite_tagesbasis * 252) - 1) * 100,
      
      SNP_ueber_Ziel =
        mu_snp_tag >= Zielrendite_tagesbasis
    )
  })
)

cat("\n--- 3-Jahres-Fenster: S&P 500 vs. Zielrendite ---\n")

print(
  summary(kontrolle_3j$SNP_Rendite_pa)
)

cat(
  "\nZielrendite p.a.:",
  round(
    unique(kontrolle_3j$Zielrendite_pa),
    2
  ),
  "%\n"
)

cat(
  "Anteil der 3-Jahres-Fenster, in denen S&P allein die Zielrendite erreicht:",
  round(
    mean(kontrolle_3j$SNP_ueber_Ziel) * 100,
    2
  ),
  "%\n"
)