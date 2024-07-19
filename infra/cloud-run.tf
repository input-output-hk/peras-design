resource "google_artifact_registry_repository" "peras-docker" {
  location      = "us-east1"
  repository_id = "peras-docker"
  description   = "Peras docker repository"
  format        = "DOCKER"

  docker_config {
    immutable_tags = true
  }
}

resource "google_artifact_registry_repository_iam_member" "member" {
  project = google_artifact_registry_repository.peras-docker.project
  location = google_artifact_registry_repository.peras-docker.location
  repository = google_artifact_registry_repository.peras-docker.name
  role = "roles/artifactregistry.admin"
  member = "serviceAccount:${var.google_service_account}"
}

resource "google_cloud_run_v2_service" "peras_server" {
  name     = "peras-server"
  location = "us-east1"
  client   = "terraform"

  depends_on = [
    google_artifact_registry_repository.peras-docker
  ]

  template {
    containers {
      image = "us-east1-docker.pkg.dev/iog-hydra/peras-docker/input-output-hk/peras-design:1ec430738accb34d622f2325ac8a0760331343f7"
      ports {
        container_port = 8091
      }
    }

    labels = {
      "commit-sha" = "1ec430738accb34d622f2325ac8a0760331343f7"
      "managed-by" = "github-actions"
    }
  }
}

resource "google_cloud_run_v2_service_iam_member" "noauth" {
  location = google_cloud_run_v2_service.peras_server.location
  name     = google_cloud_run_v2_service.peras_server.name
  role     = "roles/run.invoker"
  member   = "allUsers"
}

data "google_project" "project" {}

resource "google_cloud_run_domain_mapping" "peras_server_domain_mapping" {
  name     = "peras-simulation.cardano-scaling.org"
  location = google_cloud_run_v2_service.peras_server.location
  metadata {
    namespace = data.google_project.project.project_id
  }
  spec {
    route_name = google_cloud_run_v2_service.peras_server.name
  }
}

# Peras staging web site
resource "google_cloud_run_v2_service" "peras_staging" {
  name     = "peras-staging"
  location = "us-east1"
  client   = "terraform"

  depends_on = [
    google_artifact_registry_repository.peras-docker
  ]

  template {
    containers {
      image = "us-east1-docker.pkg.dev/iog-hydra/peras-docker/input-output-hk/peras-site:1ec430738accb34d622f2325ac8a0760331343f7"
      ports {
        container_port = 8091
      }
    }

    labels = {
      "commit-sha" = "1ec430738accb34d622f2325ac8a0760331343f7"
      "managed-by" = "github-actions"
    }
  }
}

resource "google_cloud_run_v2_service_iam_member" "noauth" {
  location = google_cloud_run_v2_service.peras_staging.location
  name     = google_cloud_run_v2_service.peras_staging.name
  role     = "roles/run.invoker"
  member   = "allUsers"
}

data "google_project" "project" {}

resource "google_cloud_run_domain_mapping" "peras_staging_domain_mapping" {
  name     = "peras-staging.cardano-scaling.org"
  location = google_cloud_run_v2_service.peras_staging.location
  metadata {
    namespace = data.google_project.project.project_id
  }
  spec {
    route_name = google_cloud_run_v2_service.peras_staging.name
  }
}
